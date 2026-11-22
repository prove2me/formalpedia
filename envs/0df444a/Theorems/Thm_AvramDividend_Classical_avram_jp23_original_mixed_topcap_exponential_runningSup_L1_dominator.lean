-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
-- name    : AvramDividend.Classical.avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:42:24.112555+00:00
-- url     : https://prove2.me/theorems/76c58cc1-2bcf-4cd2-9f96-9f7900e1c924
-- title:
--   Original mixed topcap HJB value has integrable finite-horizon exponential running-supremum envelope
-- statement:
--   Under the exact original mixed unbounded-variation finite negative Levy activity and infinite-cap HJB standing assumptions of the Avram dividend mission, select positive exponential growth parameters theta,K for w on nonnegative surplus and prove that the actual finite-horizon random envelope K exp(theta*(x+runningSup X n)) is P-integrable for every real initial surplus x and bounded horizon n. Import the independently Proved theorem avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth b63a7504 and Proved avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable 23bf6218, with real exponential addition and integrability under scalar multiplication. This is the concrete required expected prepayment occupation dominator of the root-connected original topcap physical compensated jump branch, provided the true prepayment left-limit reserve is bounded above by x+runningSup X n. The latter pathwise inequality and real stopped Campbell compensation are separate obligations; do not silently assume them.
-- source:
--   Proved original mixed topcap HJB global growth b63a7504 and original UBV all-theta runningSup exponential integrability 23bf6218.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (n : ℝ≥0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      (∀ y : ℝ, 0 ≤ y →
        w y ≤ K * Real.exp (θ * y)) ∧
      Integrable (fun ω : Ω =>
        K * Real.exp (θ * (x + runningSup X n ω))) P := by sorry
