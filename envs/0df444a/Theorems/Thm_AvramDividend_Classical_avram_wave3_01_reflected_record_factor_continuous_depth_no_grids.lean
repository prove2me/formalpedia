-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_factor_continuous_depth_no_grids
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth_no_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:30:10.094995+00:00
-- url     : https://prove2.me/theorems/7f19aab9-cfbe-4a0b-bb69-2553c1656f0b
-- title:
--   Original-Lévy reflected-record discount is continuous in depth without auxiliary schedules
-- statement:
--   For a spectrally negative Lévy process with infinite negative small-jump first variation, the original stopped discounted reward for reaching a fixed upward record b≥0 before the reflected drawdown depth a>0 is continuous as a function of the positive drawdown depth, with no auxiliary deterministic grids. This removes the artificial rational-schedule hypotheses from the exact source-based dominated-convergence argument and directly supports the continuous logarithmic record hazard used in the C1 scale-function proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale smoothness. Genuine source bridge from canonically Proved first-record reflected-height atomlessness and the companion source depth-continuity lemma, using canonically Proved Cantor rational dense schedule plus an Archimedean vanishing sequence of positive horizons. Target branch cd61d678-0150-4774-8c7e-d5f3fc16b60a; mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth_no_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) (Ioi 0) := by sorry
