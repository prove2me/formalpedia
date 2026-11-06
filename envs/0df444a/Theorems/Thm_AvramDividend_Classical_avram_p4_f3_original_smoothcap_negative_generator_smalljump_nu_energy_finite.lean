-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_smoothcap_negative_generator_smalljump_nu_energy_finite
-- name    : AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_generator_smalljump_nu_energy_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:12:08.439884+00:00
-- url     : https://prove2.me/theorems/ba8eea0b-684a-46e0-b76d-8960bf1bc889
-- title:
--   Original smooth-cap compensated negative small-jump generator has finite Lévy measure energy
-- statement:
--   The original X's compensated nonlinear C2 generator integrand is absolutely integrable over a sufficiently small negative-jump band, with the same radius valid for all predividend reserves in a compact smooth-cap interior. Original ν_integrable, a verified quadratic Taylor bound and the true source generator integrand suffice. The Lévy measure may have infinite activity near zero and C may be top. No independent process, Gaussian extraction or compensator martingale is assumed.
-- source:
--   From an exact published P4-F3 original compensated C2 Taylor quadratic bound on the same X and w, restrict negative marks to (-r,0), use r≤1 so z²=min(1,z²), apply ENNReal.ofReal monotonicity and original triplet X.ν_integrable; conclude the original small-jump generator lintegral finite uniformly in the compact localisation radius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_smoothcap_negative_jump_taylor_quadratic_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_smoothcap_negative_generator_smalljump_nu_energy_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a δ K : ℝ) (hδ : 0 < δ) (hδK : δ < K)
    (hKa : K < a) (ha : ENNReal.ofReal a < C) :
    ∃ r : ℝ, 0 < r ∧ r ≤ min δ 1 ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal
            ‖SpectrallyNegativeLevy.generatorIntegrand w u z‖ ∂X.ν) < ⊤ := by sorry
