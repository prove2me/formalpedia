-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_signed_complete_stieltjes_terminal_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_signed_complete_stieltjes_terminal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:54:37.994695+00:00
-- url     : https://prove2.me/theorems/475cf17d-bdb8-4111-a73f-e489d11ebfe3
-- title:
--   Original pre-ruin complete signed Stieltjes dividend correction through cap-linear terminal source value
-- statement:
--   For the original spectrally negative Lévy process, a finite-cap admissible strategy and a genuine pre-ruin terminal time including t=0, the real-valued discounted complete Stieltjes payout plus the cap-linear post-payment value minus the cap-linear pre-payment source value is nonpositive. The complete original dividendMeasure includes singular-continuous, absolutely continuous and atomic dividends. The cap-linear secant establishes finite real control and prevents any boundary derivative evaluation at reserve zero or cap; the source x+X_T is evaluated before the terminal right dividend. This is a terminal-source signed control comparison, not a proof of the full time-varying Lévy Itô-Meyer generator balance.
-- source:
--   Proved original-path all-mass pre-ruin cap-linear budget bf02d8bd-e937-46f3-8ca6-7c4a83a33899 (Accepted proof candidate 20546), Proved cap-linear secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52, pinned ENNReal.toReal_mono and toReal_ofReal with finite bound; actual original admissibility and right dividend increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_signed_complete_stieltjes_terminal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ y : ℝ, V y = if y ≤ c then w y else w c + (y - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω) ≤ 0 := by sorry
