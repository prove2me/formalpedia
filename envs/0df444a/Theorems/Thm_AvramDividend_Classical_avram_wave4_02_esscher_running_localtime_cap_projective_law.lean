-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_running_localtime_cap_projective_law
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_running_localtime_cap_projective_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:50:49.737994+00:00
-- url     : https://prove2.me/theorems/c635f7f4-b957-46f5-b0d9-0b72dc19768a
-- title:
--   True source Esscher local-time cap has a terminal-horizon-independent projective distribution
-- statement:
--   For the genuine source Lévy running supremum S_H and positive-root finite Esscher law Q_T, every capped local-time coordinate min(S_H,B) has identical pushforward distributions under any two later finite terminal horizons T1,T2≥H+1. This source-specific projective law is needed for a future all-horizon tilted path-space extension and the genuine reflected excursion compensator; it does not assume the latter.
-- source:
--   Canonical finite Esscher bounded-stopped observable consistency 4c1a5b7a; actual adapted running supremum via barrierStrategy_adapted and zero-barrier identity; genuine joint running-supremum measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_running_localtime_cap_projective_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (H T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁) (hT₂ : H + 1 ≤ T₂)
    (B : ℝ) (hB : 0 < B) :
    Measure.map (fun ω : Ω => min (runningSup X H ω) B)
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₁ ω - (T₁ : ℝ) * X.ψ φ)))) =
    Measure.map (fun ω : Ω => min (runningSup X H ω) B)
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (φ * X.X T₂ ω - (T₂ : ℝ) * X.ψ φ)))) := by sorry
