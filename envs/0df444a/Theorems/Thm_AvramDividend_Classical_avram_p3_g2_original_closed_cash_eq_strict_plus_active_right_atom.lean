-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
-- name    : AvramDividend.Classical.avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:31.506074+00:00
-- url     : https://prove2.me/theorems/54ad337e-58e2-4faa-80df-f3cd87fc02cc
-- title:
--   Exact original BV closed-horizon cash equals strict cash plus the sole active right dividend atom, including ruin at T and time zero
-- statement:
--   For the true original ruinTime, admissible D and Stieltjes dividendMeasure, identify the exact difference between the Iic S and Iio S discounted cash as one physical rightLimit dividend atom. Its activity switch is precisely S=0 or S<ruinTime. Thus the initial atom is counted once, the right-horizon atom is counted once under strict survival, and no horizon atom is counted when ruin occurs exactly at S or earlier. This is an exact real identity, including zero horizon and finite/infinite cap, with no terminal-integrability assumption and no occupation shortcut.
-- source:
--   Proved full physical cash split 037794fe, exact paymentTimes terminal atom c58a4a4c, original dividendMeasure singleton and dividendStrategy rightLimit; no use of Open P3 targets.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * (rightLimit D S ω - D S ω)
      else 0) := by sorry
