-- Prove2me | Theorems.Thm_CliffordHierTest_lemma_6
-- name    : CliffordHierTest.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:10.500936+00:00
-- url     : https://prove2.me/theorems/643c3011-5870-4300-8d50-2c174323c422
-- title:
--   Lemma 6 — $\min_\theta\|U-e^{i\theta}V\|_2^2=2-2|\langle U,V\rangle|$
-- statement:
--   For unitaries $U,V\in\mathcal U(d^n)$,
--   $$\min_{\theta\in[0,2\pi)}\|U-e^{i\theta}V\|_2^2=2-2|\langle U,V\rangle|.$$
--
--   It converts closeness in correlation into closeness in Frobenius norm up to a global phase.
--
--   Differences from the source:
--
--   - encoding: min over θ ∈ [0, 2π) → IsLeast of the set of values over Set.Ico 0 (2π); reason: states that the minimum exists and equals the right-hand side
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2 Lemma 6, p.5

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Lemma 6** (p.5). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For `U, V ∈ 𝒰(dⁿ)`, `min_{θ ∈ [0, 2π)} ‖U − e^{iθ} V‖₂² = 2 − 2|⟨U, V⟩|`.

**Formalization Note.** The minimum is stated as attained: `2 − 2|⟨U, V⟩|` is the least element of
the set of values `‖U − e^{iθ}V‖₂²`, `θ ∈ [0, 2π)`. `‖·‖₂` and `⟨·,·⟩` are the normalized
Frobenius norm and inner product of p.5. `d` prime is the standing assumption of §2.1. -/
theorem lemma_6 (d n : ℕ) [Fact (Nat.Prime d)] (U V : QuditUnitary d n) :
    IsLeast ((fun θ : ℝ => frobNorm ((U : QuditOperator d n) -
        Complex.exp (θ * Complex.I) • (V : QuditOperator d n)) ^ 2) '' Set.Ico 0 (2 * Real.pi))
      (2 - 2 * ‖hsInner (U : QuditOperator d n) (V : QuditOperator d n)‖) := by sorry

end CliffordHierTest
