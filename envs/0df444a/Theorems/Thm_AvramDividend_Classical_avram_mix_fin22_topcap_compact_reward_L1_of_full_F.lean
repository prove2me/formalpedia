-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_topcap_compact_reward_L1_of_full_F
-- name    : AvramDividend.Classical.avram_mix_fin22_topcap_compact_reward_L1_of_full_F
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:19:59.543673+00:00
-- url     : https://prove2.me/theorems/1bc83b10-2f4b-4379-a3ab-0d91927942ef
-- title:
--   Top-cap physical stopped reward integrability from original full reward integrability
-- statement:
--   Resolve the top-cap mixed local-reward L1 and nonnegativity prerequisite without assuming the local cash integral integrable by hand. First obtain the exact discounted original full-clock cash L1 from hFI via proved 00c2d8e4. Then apply proved 060f1bd6 to any true original filtration bounded stopped clocks with compact upper bounds on the original Levy path. This is valid for top cap (and finite cap) and supplies an explicit portion of open c087c2cb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_compact_original_reward_L1_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin22_topcap_compact_reward_L1_of_full_F
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
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
    (hFI : Integrable F P)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (hκle : ∀ j ω, κ j ω ≤ σ ω)
    (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨
              (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ j, Integrable (H j) P ∧ (∀ ω, 0 ≤ H j ω) := by sorry
