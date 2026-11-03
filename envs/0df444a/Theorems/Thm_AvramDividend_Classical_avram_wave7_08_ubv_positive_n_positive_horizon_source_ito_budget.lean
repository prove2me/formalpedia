-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
-- name    : AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T13:11:28.300771+00:00
-- url     : https://prove2.me/theorems/d457be6b-c74a-4a7e-aea2-4bb6222642d5
-- title:
--   Strictly positive ruin clock and horizon original UBV stopped Ito-Meyer cash budget
-- statement:
--   The sole nontrivial strictly-positive-clock and strictly-positive-horizon source UBV HJB expected Stieltjes payout estimate, retaining original Ω/P/filtration/X, source admissible dividend D, generator, stopped ruinTime and full paymentTimes. It needs original controlled mixed Gaussian and compensated small-jump Ito-Meyer with source martingale centring and boundary positivity.
-- source:
--   Exact T>0 branch of positive-clock original-source theorem 665b3b52-1f20-4307-8905-5b429a0f6425. Newly Proved all-n zero-horizon source Stieltjes bound a4ec4831-8af1-49f2-b115-bdf9a26b27b4 closes T=0. Publication does not itself prove this remaining stochastic child or its parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
