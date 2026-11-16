-- Prove2me | Theorems.Thm_CompetingSellers_Supplement_theorem_1_4_misaligned_model
-- name    : CompetingSellers.Supplement.theorem_1_4_misaligned_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:34:09.214382+00:00
-- url     : https://prove2.me/theorems/168c3255-40de-426e-bdc1-98cf320c6365
-- title:
--   Theorem 1.4 (Misaligned Model) — Alice earns $(a-b)^+$ in every equilibrium; the set of payoff triples is exactly determined
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with a null message and let $a,b>0$. In the **misaligned model** Alice commits to a mechanism, Bob responds, and the buyer must visit Bob first. Then:
--
--   1. in every Stackelberg equilibrium $(A,\mathcal M)$, Alice's expected revenue is her Bertrand revenue $(a-b)^+$;
--   2. if $a\le b$, there are two Stackelberg equilibria with different revenues of Bob and different expected utilities of the buyer;
--   3. the set of equilibrium payoff triples (Alice's expected revenue, Bob's expected revenue, the buyer's expected utility) is exactly
--   $$\begin{cases}\{(a-b,\,0,\,b)\},&a>b,\\ \{(0,\,b-u,\,u):u\in[0,a]\},&a\le b.\end{cases}$$
--
--   Commitment alone does not let Alice beat Bertrand competition: when the buyer must visit Bob first, Bob undercuts her after she commits. For $a\le b$, Alice's choice of mechanism decides only how Bob and the buyer split the surplus.
--
--   **Formalization Note** Revenues, plans and the buyer's utility are the fixed-order ones with Bob first (`revenueFrom … bob`, `orderUtil … bob`). The buyer's utility in a triple is his maximum expected utility over plans visiting Bob first.
--
--   Differences from the source:
--
--   - reading: when a ≤ b, the revenue of Bob and the utility of the buyer are not uniquely determined → two Stackelberg equilibria with different Bob revenues and different buyer utilities; reason: the literal meaning of "not uniquely determined" for both quantities
--   - encoding: the set of equilibrium payoff triples → {eqPayoffsFrom a b bob A (𝓜 A) : (A, 𝓜) a Stackelberg equilibrium of the misaligned model} ⊆ ℝ × ℝ × ℝ; reason: payoffs are the real-valued revenues and the buyer's utility util_BA; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Theorem 1.4, p.38 (PDF 41); first stated p.6 (PDF 9)

import Mathlib
import Definitions.Def_CompetingSellers_Supplement_IsStackelbergEqFrom

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers.Supplement

/-- **Theorem 1.4 (Misaligned Model).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Theorem 1.4, p.38 (PDF 41; first stated p.6, PDF 9): "Consider an
instance of the duopoly game in the misaligned model with fixed buyer values `a, b > 0`. In every
Stackelberg equilibrium, Alice earns her Bertrand revenue `(a − b)⁺`. When `a ≤ b`, the revenue of
Bob and the utility of the buyer are not uniquely determined. The set of equilibrium payoff
triples, Alice's expected revenue, Bob's expected revenue, and the buyer's expected utility, is
exactly `{(a − b, 0, b)}` if `a > b`, `{(0, b − u, u) : u ∈ [0, a]}` if `a ≤ b`. Here, `u` denotes
the buyer's expected utility."

**Formalization Note.** The misaligned model is the fixed-order model with first seller `bob`
(`revenueFrom … bob`, `orderUtil … bob`); `Σ` is quantified as in Theorem 1.1. The set of
equilibrium payoff triples is `{eqPayoffsFrom a b bob A (𝓜 A) : (A, 𝓜) a Stackelberg
equilibrium}`, an equality of subsets of `ℝ × ℝ × ℝ`. "Not uniquely determined" is stated
explicitly: two equilibria with different Bob revenues and different buyer utilities. -/
theorem theorem_1_4_misaligned_model (S : Type) [MeasurableSpace S] [StandardBorelSpace S]
    [Uncountable S] (null : S) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ (A : Mech S null) (𝓜 : Mech S null → Mech S null),
      IsStackelbergEqFrom a b Seller.bob A 𝓜 →
        revenueFrom a b Seller.bob A (𝓜 A) Seller.alice = max (a - b) 0) ∧
    (a ≤ b → ∃ (A A' : Mech S null) (𝓜 𝓜' : Mech S null → Mech S null),
      IsStackelbergEqFrom a b Seller.bob A 𝓜 ∧ IsStackelbergEqFrom a b Seller.bob A' 𝓜' ∧
      revenueFrom a b Seller.bob A (𝓜 A) Seller.bob ≠
        revenueFrom a b Seller.bob A' (𝓜' A') Seller.bob ∧
      orderUtil a b A (𝓜 A) Seller.bob ≠ orderUtil a b A' (𝓜' A') Seller.bob) ∧
    (b < a → {p : ℝ × ℝ × ℝ | ∃ (A : Mech S null) (𝓜 : Mech S null → Mech S null),
        IsStackelbergEqFrom a b Seller.bob A 𝓜 ∧ eqPayoffsFrom a b Seller.bob A (𝓜 A) = p} =
      {(a - b, 0, b)}) ∧
    (a ≤ b → {p : ℝ × ℝ × ℝ | ∃ (A : Mech S null) (𝓜 : Mech S null → Mech S null),
        IsStackelbergEqFrom a b Seller.bob A 𝓜 ∧ eqPayoffsFrom a b Seller.bob A (𝓜 A) = p} =
      (fun u : ℝ => ((0 : ℝ), b - u, u)) '' Set.Icc 0 a) := by sorry

end CompetingSellers.Supplement
