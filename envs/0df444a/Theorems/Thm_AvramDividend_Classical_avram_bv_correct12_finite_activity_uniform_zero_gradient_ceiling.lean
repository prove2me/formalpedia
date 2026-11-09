-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:19:12.226886+00:00
-- url     : https://prove2.me/theorems/9db99eb1-f7fd-43e7-b8d2-a6a2a4dbaabd
-- title:
--   Original finite-activity Standing BV HJB gives a derivative ceiling uniform down to zero on every bounded reserve strip
-- statement:
--   For the original spectrally negative Standing BV process with finite total negative jump intensity, positive discount, strictly positive dividend cap and the exact original interior HJB and gradient hypotheses, the candidate derivative is uniformly bounded from above on each bounded reserve strip, including reserves arbitrarily close to zero. The estimate uses positive drift, finite negative jump rate, the nonnegative values at actual negative jump destinations and the candidate value bound from continuity. It is a necessary deterministic regularity interface for de-localising the finite-activity original stopped source near zero; it does not assert the stopped martingale or cash reward identity.
-- source:
--   Needed by original finite-activity physical stopped source 8df3cb52 and finite-cap stopped HJB source 73419313: correct zero-reserve boundary control for the true original X and w without assuming a derivative bound away from zero or a global B-L1 source. Uses Proved e6d7e520, Proved f138f64f, Proved 00de5b03 and Standing positive drift 0432f641.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y : ℝ, 0 < y → y ≤ b → ENNReal.ofReal y < C → deriv w y ≤ L := by sorry
