-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_18
-- name    : CliffordHierTest.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:18.964649+00:00
-- url     : https://prove2.me/theorems/159dba91-833c-4871-b6b5-1dde5cb7eebf
-- title:
--   Lemma 18 — separation lemma for Pauli polynomials
-- statement:
--   Let $d$ be prime, $k\ge0$, and $U\in\mathcal P^{(k)}$ with
--   $$\|U-I\|_2\le\delta<2^{-k+3/2}.$$
--   Then $U=e^{i\theta}I$ for some $\theta\in[-2\delta,2\delta]$.
--
--   Pauli polynomials close to the identity are scalars, with a quantitative bound on the phase.
--
--   Differences from the source: none.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §4 Lemma 18, p.8

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 18** (separation lemma) (p.8). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
Let `k ≥ 0` and `U ∈ 𝒫^{(k)}` with `‖U − I‖₂ ≤ δ < 2^{-k+3/2}`. Then `U = e^{iθ} I` for some
`θ ∈ [−2δ, 2δ]`.

**Formalization Note.** `2^{-k+3/2}` is the real power `(2:ℝ) ^ (-(k:ℝ) + 3/2)`; both inequalities
as printed. `d` prime (§2.1). -/
theorem lemma_18 (d n : ℕ) [Fact (Nat.Prime d)] (k : ℕ) (U : QuditUnitary d n)
    (hU : U ∈ pauliPoly d n k) (δ : ℝ) (hδ : frobNorm ((U : QuditOperator d n) - 1) ≤ δ)
    (hδk : δ < (2 : ℝ) ^ (-(k : ℝ) + 3 / 2)) :
    ∃ θ ∈ Set.Icc (-2 * δ) (2 * δ),
      (U : QuditOperator d n) = Complex.exp (θ * Complex.I) • (1 : QuditOperator d n) := by sorry

end CliffordHierTest
