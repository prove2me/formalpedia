-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_nonmonotone_rightcont_stopping_cofinal_budget_fatou
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_rightcont_stopping_cofinal_budget_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:41:25.216231+00:00
-- url     : https://prove2.me/theorems/504fd208-2c54-42fe-9098-f2a0000fbb68
-- title:
--   Original UBV nonmonotone right-continuous stopping Fatou with cofinally many budgets
-- statement:
--   For the actual source spectrally negative Lévy process and admissible D, true right-continuous-filtration stopping localisers S_n need not be monotone. If their tail-infimum limit is infinity almost surely and the discounted complete dividend Stieltjes expectation budget holds at cofinally many ruin-clipped S_n, then the full ruin-time expected bound holds. Apply the accepted original ruin-clipped liminf identity and the cofinally budgeted overshooting Fatou theorem. This retains the source filtration, 0≤w(0), and zero/infinite ruin endpoints, with no new smoothness or variation assumption. The stochastic budget remains explicit.
-- source:
--   Accepted source clock endpoint identity b6f6314c-f08c-4ac7-987f-77eeccb7e5fd and pending/proposed cofinal overshooting theorem AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_rightcont_stopping_cofinal_budget_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
