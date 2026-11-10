-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:50:49.716468+00:00
-- url     : https://prove2.me/theorems/fdff2585-b485-4f00-a395-928413a4054e
-- title:
--   Original zero-jump top-cap prepayment reserve has bounded-stop discounted L1
-- statement:
--   For the same original Standing spectrally negative Lévy X, admissible dividend process D, and genuine bounded right-continuous stopping clock sigma, obtain integrability of discounted w(riskProcess X x D sigma). HJB global exponential growth, nonnegative original dividends and a bounded stopped raw Lévy exponential moment give exact prepayment terminal L1 at infinite spatial cap, with no new stochastic process.
-- source:
--   Direct L1 component of canonical strict source c63d897f which feeds zero-nu topcap witness 249c532d and 6c6f8a07; Proved 9258c362, b91875a4, 5224d9f0, 2159c88b, 0e054a59.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original positive-Gaussian top-cap prepayment terminal is L1 at
    bounded true stopping clocks; no right dividend is deducted at the clock. -/

theorem AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω => Real.exp (-(q * (σ ω : ℝ))) *
      w (riskProcess X x D (σ ω) ω)) P := by sorry
