-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_3_10
-- name    : ElimAgree.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:36:26.762207+00:00
-- url     : https://prove2.me/theorems/8d81735b-6ca7-4fb2-b3a4-f7eaf25c83a4
-- title:
--   Theorem 3.10 (One majority bit) — error $2^{-k}\beta_k(\delta)$ with one bit from Bob
-- statement:
--   Let $f_1,\dots,f_k$ be Boolean functions on finite domains which all have uniform sign correlation $\delta$ (3.4). Then there is a public-coin protocol for $\mathrm{Elim}(f_1,\dots,f_k)$ in which Bob sends one bit and Alice outputs, with error at most
--
--   $$2^{-k}\beta_k(\delta)\qquad\text{on every input},\qquad \beta_k(\delta)=2\Pr\big[Z<\tfrac k2\big]+\Pr\big[Z=\tfrac k2\big],\ Z\sim\mathrm{Bin}\big(k,\tfrac{1+\delta}2\big).$$
--
--   In particular, for every $0<\delta\le1$,
--
--   $$\beta_k(\delta)\le2e^{-k\delta^2/2}.$$
--
--   With the sign primitive for disjointness (Lemma 3.11) this shows that one bit suffices for local-output elimination of $k=\Theta(n^2)$ disjointness instances.
--
--   **Formalization Note** The protocol is a distribution over trees in which only Bob speaks and which have depth at most one.
--
--   Differences from the source:
--   - encoding: Bob sends one bit → trees with only Bob nodes and depth ≤ 1; reason: a depth-0 tree can be padded by a Bob node with two equal children; the error is unchanged
--   - reading: "In particular β_k(δ) ≤ 2e^{−kδ²/2}" for the δ of the hypothesis → for every 0 < δ ≤ 1; reason: a uniform sign correlation of a function on a nonempty domain is at most 1, since |χE[ab]| ≤ 1; for δ > 1, (1 + δ)/2 is not a probability
--   - encoding: sign functions a, b and a distribution on pairs → Bool-valued functions read through sgn; a law on the finite set of pairs; reason: same objects
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.10, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_SignCorr

namespace ElimAgree

namespace Supplement

/-- Theorem 3.10 (One majority bit), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.11. Suppose
`f_1, …, f_k` all have uniform sign correlation `δ`. There is a public-coin protocol in which Bob
sends one bit and Alice outputs, with error at most `2^{−k} β_k(δ)` on every input, where
`β_k(δ) = 2 Pr[Z < k/2] + Pr[Z = k/2]`, `Z ∼ Bin(k, (1 + δ)/2)`. In particular
`β_k(δ) ≤ 2e^{−kδ²/2}`.

**Formalization Note.** The protocol is a `PMF` over trees with only Bob's nodes and depth at most
one, whose leaves carry Alice's output as a function of her input. The input types of the `f_i` may
differ. The "in particular" clause is stated for every `0 < δ ≤ 1`; a uniform sign correlation of a
function on a nonempty domain is at most `1`. -/
theorem theorem_3_10 :
    (∀ (k : ℕ) (X Y : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
      [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] (f : ∀ i, X i → Y i → Bool) (δ : ℝ),
      (∀ i, HasUniformSignCorr (f i) δ) →
      ∃ μ : PMF (AliceProt (∀ i, X i) (∀ i, Y i) (Fin k → Bool)),
        (∀ T ∈ μ.support, IsOneWayBA T) ∧ CostLE μ 1 ∧
        ∀ x y, aliceErr (elimAns f) μ x y ≤ ENNReal.ofReal (betaK k δ / 2 ^ k)) ∧
    (∀ (k : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → betaK k δ ≤ 2 * Real.exp (-(k * δ ^ 2 / 2))) := by sorry

end Supplement

end ElimAgree
