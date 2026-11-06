-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_1
-- name    : CompetingSellers.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:47.769407+00:00
-- url     : https://prove2.me/theorems/bd18b6fc-fbea-4baa-a298-ac2fadbe8981
-- title:
--   Lemma 3.1 — buyer behaviour through the effective values $a|_B$ and $b|_A$
-- statement:
--   Let Alice and Bob use mechanisms $A$ and $B$ (identified with their proper pricing representations), and put $a|_B=a-\mathrm{Aug}_B(a,b)$, $b|_A=b-\mathrm{Aug}_A(b,a)$, $b|_a=\max(0,b-a)$, $a|_b=\max(0,a-b)$.
--
--   1. $\mathrm{util}_{AB}(A,B)=\mathrm{util}_A(a|_B)+\mathrm{util}_B(b)$ and $\mathrm{util}_{BA}(A,B)=\mathrm{util}_B(b|_A)+\mathrm{util}_A(a)$.
--   2. If the buyer's selected plan visits Alice first, it takes from Alice the allocation $x_A=z^-_A(a|_B)$ if $z^+_B(b)>z^+_B(b|_a)$ and $x_A=z^+_A(a|_B)$ otherwise, then from Bob $z^+_B(b|_a)$ after winning Alice's good and $z^+_B(b)$ after losing it (on branches of positive probability). If it visits Bob first, it takes $z^+_B(b|_A)$ from Bob, then $z^+_A(a|_b)$ from Alice after winning Bob's good and $z^+_A(a)$ after losing it.
--   3. If the buyer visits Alice first, $\mathrm{rev}_A(A,B)=A(x_A)$ and
--   $$\mathrm{rev}_B(A,B)=\big(1-z^-_A(a|_B)\big)B\big(z^+_B(b)\big)+z^-_A(a|_B)\,B\big(z^+_B(b|_a)\big);$$
--   if he visits Bob first, $\mathrm{rev}_B(A,B)=B(z^+_B(b|_A))$ and $\mathrm{rev}_A(A,B)=(1-z^+_B(b|_A))A(z^+_A(a))+z^+_B(b|_A)A(z^+_A(a|_b))$; all these prices are finite.
--
--   The lemma reduces the two-seller buyer problem to two monopolist problems at effective values.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - reading: items 2–3 "when the buyer interacts with Alice (Bob) first" → statements about the buyer's selected plans with that first seller, second-seller choices on branches of positive probability; reason: the lemma describes the tie-broken equilibrium play; Definition 2.1's convention for unreached branches
--   - reading: "an analogous result holds except that the buyer always picks the option z⁺_B(b|_A) from Bob"; "The case when the buyer interacts with Bob first is analogous" → the Bob-first choices z⁺_B(b|_A), z⁺_A(a|_b), z⁺_A(a) and revenues B(z⁺_B(b|_A)), (1 − z⁺_B(b|_A))A(z⁺_A(a)) + z⁺_B(b|_A)A(z⁺_A(a|_b)) written out; reason: the analogous statements, in the form the paper itself uses on p.61
--   - encoding: x_A's second case "if z⁺_B(b) = z⁺_B(b|_a)" → the else branch of z⁺_B(b|_a) < z⁺_B(b); reason: z⁺_B is non-decreasing and b|_a ≤ b, so the cases are exhaustive; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.1, pp.19–20 (PDF 22–23); Bob-first revenue form p.61 (PDF 64)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.1 (buyer behaviour through effective values).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.1, pp.19–20 (PDF 22–23): "Let Alice and Bob use mechanisms `A` and `B`
respectively. Define the quantities `a|_B = a − Aug_B(a, b)` and `b|_A = b − Aug_A(b, a)`.
1. The maximum utility the buyer can obtain when interacting with Alice first (denoted
`util_AB(A, B)`) and when interacting with Bob first (denoted `util_BA(A, B)`) respectively is:
`util_AB(A, B) = util_A(a|_B) + util_B(b)` and `util_BA(A, B) = util_B(b|_A) + util_A(a)`.
2. When the buyer interacts with Alice first, the utility in Item 1 is attained by first picking
the option `x_A` from Alice, where `x_A = z⁻_A(a|_B)` if `z⁺_B(b) > z⁺_B(b|_a)`, and
`x_A = z⁺_A(a|_B)` if `z⁺_B(b) = z⁺_B(b|_a)`, and then picking the option `z⁺_B(b|_a)` from Bob if
he receives Alice's item, and the option `z⁺_B(b)` from Bob otherwise. When the buyer interacts
with Bob first, our tie breaking implies that an analogous result holds except that the buyer
always picks the option `z⁺_B(b|_A)` from Bob.
3. When the buyer interacts with Alice first, his payments to Alice and Bob are (here, `x_A` is
as defined above): `rev_A(A, B) = A(x_A)`,
`rev_B(A, B) = (1 − z⁻_A(a|_B)) · B(z⁺_B(b)) + z⁻_A(a|_B) · B(z⁺_B(b|_a))`. The case when the
buyer interacts with Bob first is analogous."

**Formalization Note.** `util_A`, `z±_A`, `Aug_A`, `A(x)` are those of Alice's proper pricing
representation `P_A = priceRep a A` (Bob's: `priceRep b B`), as on p.18. Items 2–3 are stated for
the buyer's selected (tie-broken) plans; the second-seller choices are stated on branches reached
with positive probability. The analogous Bob-first statements are spelled out: the buyer picks
`z⁺_B(b|_A)` from Bob, then `z⁺_A(a|_b)` from Alice after winning Bob's good and `z⁺_A(a)`
otherwise, and `rev_B = B(z⁺_B(b|_A))`,
`rev_A = (1 − z⁺_B(b|_A)) · A(z⁺_A(a)) + z⁺_B(b|_A) · A(z⁺_A(a|_b))` (as used on p.61). -/
theorem lemma_3_1 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : Mech S null) :
    let aB := a - mAug b B a b
    let bA := b - mAug a A b a
    let xAl := if mZPlus b B (max 0 (b - a)) < mZPlus b B b then mZMinus a A aB
      else mZPlus a A aB
    (orderUtil a b A B Seller.alice = mUtil a A aB + mUtil b B b ∧
      orderUtil a b A B Seller.bob = mUtil b B bA + mUtil a A a) ∧
    ((∀ π ∈ selectedPlans a b A B, π.first = Seller.alice →
        π.firstAlloc A B = xAl ∧ (0 < xAl → π.allocW A B = mZPlus b B (max 0 (b - a))) ∧
          (xAl < 1 → π.allocL A B = mZPlus b B b)) ∧
      ∀ π ∈ selectedPlans a b A B, π.first = Seller.bob →
        π.firstAlloc A B = mZPlus b B bA ∧
          (0 < mZPlus b B bA → π.allocW A B = mZPlus a A (max 0 (a - b))) ∧
          (mZPlus b B bA < 1 → π.allocL A B = mZPlus a A a)) ∧
    (BuyerFirst a b A B Seller.alice →
      priceRep a A xAl ≠ ⊤ ∧ priceRep b B (mZPlus b B b) ≠ ⊤ ∧
      priceRep b B (mZPlus b B (max 0 (b - a))) ≠ ⊤ ∧
      revenue a b A B Seller.alice = (priceRep a A xAl).toReal ∧
      revenue a b A B Seller.bob =
        (1 - mZMinus a A aB) * (priceRep b B (mZPlus b B b)).toReal +
          mZMinus a A aB * (priceRep b B (mZPlus b B (max 0 (b - a)))).toReal) ∧
    (BuyerFirst a b A B Seller.bob →
      priceRep b B (mZPlus b B bA) ≠ ⊤ ∧ priceRep a A (mZPlus a A a) ≠ ⊤ ∧
      priceRep a A (mZPlus a A (max 0 (a - b))) ≠ ⊤ ∧
      revenue a b A B Seller.bob = (priceRep b B (mZPlus b B bA)).toReal ∧
      revenue a b A B Seller.alice =
        (1 - mZPlus b B bA) * (priceRep a A (mZPlus a A a)).toReal +
          mZPlus b B bA * (priceRep a A (mZPlus a A (max 0 (a - b)))).toReal) := by sorry

end CompetingSellers
