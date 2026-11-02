-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
-- name    : AvramDividend.Classical.avram_wave5_04b_closed_preruin_actual_postpayment_solvency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:05:39.1672+00:00
-- url     : https://prove2.me/theorems/f23e585c-2efa-4b14-a85f-49b65e011baa
-- title:
--   Full original stopped closed-window postpayment solvency including zero and cap
-- statement:
--   Under the exact original IsAdmissibleLe capped dividend condition, at every sample path and every nonnegative finite horizon T that is zero or strictly before ruin, the original postpayment reserve x+X_s-D_s^+ is nonnegative at every real time s in [0,T], including s=0 and both cap boundaries. No strict interior hloc. This supplies the window hSolvent argument for the derivative-free real signed Stieltjes secant theorem.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- Genuine postpayment solvency holds throughout every original pre-ruin closed
--   time window, including time zero and boundary reserve zero/cap contacts. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞)
--       (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
--       (ω : Ω) (T : ℝ≥0)
--       (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
--       ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
--         0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω := by
--     intro s hs
--     have hs0 : 0 ≤ s := hs.1
--     have hsT : s ≤ (T : ℝ) := hs.2
--     have hrepr : (s.toNNReal : ℝ) = s := Real.coe_toNNReal hs0
--     have hleReal : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
--       simpa only [hrepr] using hsT
--     have hle : s.toNNReal ≤ T := by
--       exact_mod_cast hleReal
--     have hPreS : s.toNNReal = 0 ∨
--         (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
--       rcases hPre with hTzero | hTlt
--       · left
--         apply le_antisymm
--         · simpa only [hTzero] using hle
--         · exact zero_le _
--       · right
--         have hcoe : (s.toNNReal : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
--           exact_mod_cast hle
--         exact lt_of_le_of_lt hcoe hTlt
--     have hAdmissible : IsAdmissible X x D := hD.1
--     have hCover := hAdmissible.2 ω s.toNNReal hPreS
--     dsimp [riskProcess] at hCover
--     linarith only [hCover]

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_closed_preruin_actual_postpayment_solvency

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
      0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω := by sorry
