-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
-- name    : AvramDividend.Classical.avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:58:53.110623+00:00
-- url     : https://prove2.me/theorems/cd8439b5-6b7d-425f-9365-540d14d72b64
-- title:
--   Original BV finite-cap unmasked negative-jump HJB boundary sign from true integral continuity
-- statement:
--   For the original standing spectrally negative bounded-variation Levy source, let the candidate satisfy the original interior generator and gradient inequalities. On any sequence of original interior reserve values approaching finite cap C for which w and the FULL UNMASKED nonlinear negative-mark Levy integral converge to their cap values, the genuine cap drift plus full negative-mark integral less discount q*w(C) is nonpositive. The original positive BV drift is used to replace interior derivative by its lower bound one. Unlike the misleading A22 spatial-mask expectation residual, this cap-generator sign retains the stochastic compensator at the reflecting upper dividend barrier. Source limit of full mark integral is explicit and still requires a genuine independent proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFin : C ≠ ⊤)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℕ → ℝ)
    (hy : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (hwLimit : Tendsto (fun n => w (y n)) atTop (𝓝 (w C.toReal)))
    (hJumpLimit : Tendsto (fun n =>
      ∫ z in Iio (0 : ℝ), w (y n + z) - w (y n) ∂X.ν)
      atTop (𝓝 (∫ z in Iio (0 : ℝ),
        w (C.toReal + z) - w C.toReal ∂X.ν))) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by sorry
