-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:31:38.198982+00:00
-- url     : https://prove2.me/theorems/8f44cfc2-44b9-48e2-b567-d6db712e493a
-- title:
--   True original top-cap strict pre-ruin signed cash on prefix of a later stopped physical grid
-- statement:
--   For an actual top-cap stopped physical grid whose earlier prefix clock is strictly before ruin, the original signed payment-potential prefix together with inclusive original dividend cash and initial atom is bounded by its genuine right-limit discounted Stieltjes mesh error. The exact canonical prefix identification and already Proved strict top-cap full-grid cash bound are used without a finite-jump restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_prefix_double_clip_signed_grid_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t ρ : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j i : ℕ) (htn : t ≤ (n : ℝ≥0))
    (hi : i ≤ (n + 1) * (j + 1))
    (hti : t = min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ) :
    let u : ℕ → ℝ≥0 := fun l =>
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ l ∈ Finset.range i,
        Real.exp (-(q * (u (l + 1) : ℝ))) *
          (w (x + X.X (u (l + 1)) ω - rightLimit D (u (l + 1)) ω) -
           w (x + X.X (u (l + 1)) ω - rightLimit D (u l) ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal := by sorry
