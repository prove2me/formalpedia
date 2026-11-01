-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_joint_regulator_reflection_projective_law
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_joint_regulator_reflection_projective_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:04:25.59099+00:00
-- url     : https://prove2.me/theorems/858dee7d-0e14-4220-9f59-59be76c1b886
-- title:
--   Actual Esscher regulator and reflected drawdown have a joint terminal-horizon-independent law
-- statement:
--   For the actual SNLP X with positive Esscher root, any fixed horizon H and later terminal Esscher laws Q_T1 and Q_T2, the entire joint distribution of the running-record local time S_H and reflected drawdown R_H is the same. This is a finite-coordinate projective consistency fact for construction of a canonical path-space tilted reflected law; no excursion marks, intensity, or compensator are presumed.
-- source:
--   Generic bounded stopped-history observable Esscher terminal consistency 4c1a5b7a, actual reflectedSup_adapted 63c373fc, actual barrierStrategy_adapted and runningSup identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_joint_regulator_reflection_projective_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (H T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁) (hT₂ : H + 1 ≤ T₂) :
    Measure.map (fun ω : Ω => (runningSup X H ω, reflectedSup X H ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₁ ω - (T₁ : ℝ) * X.ψ φ)))) =
    Measure.map (fun ω : Ω => (runningSup X H ω, reflectedSup X H ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₂ ω - (T₂ : ℝ) * X.ψ φ)))) := by sorry
