-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
-- name    : AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:37:47.117097+00:00
-- url     : https://prove2.me/theorems/00c2d8e4-8201-4562-8c9f-4718d1e95102
-- title:
--   Integrable original stopped F forces closed Stieltjes dividend cash L1 at the same physical clock
-- statement:
--   For an admissible original unbounded-variation dividend strategy and any original right-continuous stopping clock, if the exact stopped reward F is integrable, its nonnegative closed-Iic discounted Stieltjes cash component is integrable. The post-right-payment terminal is nonnegative on every zero, surviving, ruin and cap branch, so closed cash lies between zero and F. The random clock cash is measurable by the original dividend-source measurability theorem. This is a finite- and top-cap endpoint integrability interface for the strict stopped witness sources d1caa4aa and 4a699fd8, without Gaussian centring.
-- source:
--   Root-connected source-exact endpoint integrability for d1caa4aa and 4a699fd8; Proved f6fef241 (terminal nonnegative), d12a741a (stopping clock measurable), 2d478c7d (original complete Stieltjes cash measurable). No horizon cash L1 assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P := by sorry
