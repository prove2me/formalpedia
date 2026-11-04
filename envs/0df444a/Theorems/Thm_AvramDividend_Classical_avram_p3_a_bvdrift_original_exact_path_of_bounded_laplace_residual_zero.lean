-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:28:27.175483+00:00
-- url     : https://prove2.me/theorems/c540bf8f-3173-41b1-b84f-a8547dabcfcb
-- title:
--   Original BV physical-drift jump path from bounded integer residual Laplace identities
-- statement:
--   On the same original probability space, original spectrally negative Levy process, and its exact bounded-variation characteristics, if the bounded Laplace deficit of the actual raw-jump-removed physical-drift residual is integrable and has zero expectation at every integer clock, then for almost every source path and every real nonnegative time, X_t equals t times its source physical drift minus the sum of its actual negative left jump magnitudes. The original source residual and its Laplace conditions are explicitly defined by the statement, with no replacement process or fictitious compensator. The missing unconditional Levy-characteristic/P2 jump-law calculation remains a distinct proof obligation.
-- source:
--   Conditional corollary of original raw residual monotonicity e9d95081 and exact bounded-Laplace monotone-clock lemma 7fbc19d7. The latter's accepted proof must be verified before submitting this dependent proof. Source X.X_zero and algebra complete the identity. This does NOT prove the Laplace assumptions from ψ or ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_exact_path_of_bounded_laplace_residual_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
    (∀ n : ℕ, Integrable
      (fun ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) P) →
    (∀ n : ℕ, (∫ ω, 1 - Real.exp (-(R (n : ℝ≥0) ω)) ∂P) = 0) →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
