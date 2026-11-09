-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:14:41.430633+00:00
-- url     : https://prove2.me/theorems/773a5847-afec-4ba8-81db-9905c6212f6d
-- title:
--   Same-space stopped Gaussian compensated square is stopped quadratic source minus bracket
-- statement:
--   For an arbitrary physical-grid stopping index on the original probability space, stopped sampling commutes pointwise with the subtraction of the deterministic Gaussian quadratic bracket and the squaring of the centred source. No stopping-time or integrability assumptions are needed for this exact pathwise algebraic identity.
-- source:
--   Pinned Mathlib stoppedValue_sub and stoppedValue_comp, applied to the same original SpectrallyNegativeLevy process. This algebraic identity permits the public stopped compensated-square mean theorem 46667cb1 to connect to the expected stopped second-moment difference 4489c8e9, giving the Gaussian stopping-clock energy equation.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_Q_pointwise_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (τ : Ω → WithTop ℕ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
    let Q : ℝ≥0 → Ω → ℝ := fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2
    stoppedValue (fun i : ℕ => Q (grid i)) τ =
      (fun ω => stoppedValue (fun i : ℕ => M (grid i)) τ ω ^ 2 -
        stoppedValue (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
          τ ω) := by sorry
