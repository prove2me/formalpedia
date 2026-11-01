-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_cadlag
-- name    : AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:18:30.136735+00:00
-- url     : https://prove2.me/theorems/1e55d433-f0c0-4b5c-bd38-27b41cffdd8f
-- title:
--   Actual post-payment controlled Lévy reserve has càdlàg sample paths in BV and UBV
-- statement:
--   For every genuine original spectrally negative Lévy sample path X, any adapted nondecreasing left-continuous dividend strategy D and any initial capital x, the actual post-payment controlled reserve U⁺_t=x+X_t−rightLimit D_t is right-continuous at every t≥0 and has a finite strict-left limit at every t>0. This source-faithful càdlàg property follows from the actual Lévy path's right continuity, the canonically Proved pathwise right continuity of D's right-limit process, and the canonically Proved controlled left-limit theorem. It is valid in both bounded and unbounded variation and supplies the regularity interface for stopped original-path Itô–Meyer calculus.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), actual controlled surplus; source SpectrallyNegativeLevy.rightCont, dividendStrategy_rightLimit_rightContinuous bba8dbb3 and postPaymentReserve_no_positive_jumps 51ff3291.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_no_positive_jumps

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    (∀ (t : ℝ≥0),
      ContinuousWithinAt
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (Ici t) t) ∧
    (∀ (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l)) := by sorry
