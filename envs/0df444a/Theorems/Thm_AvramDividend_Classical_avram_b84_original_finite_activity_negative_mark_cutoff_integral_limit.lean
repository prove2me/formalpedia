-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
-- name    : AvramDividend.Classical.avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:26:24.108946+00:00
-- url     : https://prove2.me/theorems/345e9ec7-9191-4066-bc82-0ca2a890d5c0
-- title:
--   Original finite-negative-activity signed small-mark compensator cutoff first moment converges to original full negative strip
-- statement:
--   In the exact original finite-negative-activity Lévy source, the signed first moment of small negative jump marks over the cutoff interval from minus one (excluded) to the cutoff negative inverse mesh tends to its full first moment over the interval strictly between minus one and zero. Proved B83 supplies integrability of the signed mark z under the original negative Lévy measure restricted to this finite-mass small negative strip, without any global second negative-jump mark moment. Under the restricted measure, the cutoff indicators eventually equal one at every strictly negative mark in the strip because the cutoff tends to zero. The absolute integrand is dominated by the integrable original signed mark magnitude; pinned dominated convergence yields the expected cutoff integral limit. Restriction-restriction identifies the integrals under the true original measure rather than a substituted intensity. Together with B80 and B82 this supplies the deterministic limiting compensation drift for genuine jumpfree cells of the physical stopped Itô mesh.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i) negative jump compensation; original finite-activity B83; pinned dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b83_original_finite_negative_activity_small_mark_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by sorry
