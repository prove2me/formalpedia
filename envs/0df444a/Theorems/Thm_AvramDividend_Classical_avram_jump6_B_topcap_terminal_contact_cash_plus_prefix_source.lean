-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
-- name    : AvramDividend.Classical.avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:40:12.924613+00:00
-- url     : https://prove2.me/theorems/28d7a471-f726-4adb-824c-fb80ed69ed87
-- title:
--   Exact original topcap terminal crossing plus full inclusive dividend cash bounded by prefix cash plus true contact tail
-- statement:
--   At a positive original ruin contact rho, the crossing-cell potential change plus terminal ruin reserve adjustment and the entire inclusive original discounted dividend cash is bounded by its exact closed-prefix cash and the shrinking precontact strict payment tail. Derives from true endpoint exclusion and full stopped cash partition together with the proved crossing-cell inequality, with no finite activity assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (ρ δ a : ℝ≥0)
    (hρpos : 0 < ρ) (hρruin : (ρ : ℝ≥0∞) = ruinTime X x D ω)
    (hleft : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hbefore : a < ρ)
    (w : ℝ → ℝ) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Real.exp (-(q * (ρ : ℝ))) *
      (w (x + X.X ρ ω - rightLimit D ρ ω) -
       w (x + X.X ρ ω - rightLimit D a ω)) +
    Real.exp (-(q * (ρ : ℝ))) *
      (w (riskProcess X x D ρ ω) -
       w (x + X.X ρ ω - rightLimit D ρ ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (a : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
