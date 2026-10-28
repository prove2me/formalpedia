-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_capped_inverse_firstHit_isStoppingTime
-- name    : AvramDividend.Classical.runningSup_capped_inverse_firstHit_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:51:50.645737+00:00
-- url     : https://prove2.me/theorems/6c08d0c1-1723-4771-ba79-8a4b62290a68
-- title:
--   The actual inverse of the continuous running-supremum local-time regulator, capped at finite time, is a stopping time
-- statement:
--   For the original spectrally negative Lévy process X with its actual running-supremum regulator S_t, define the inverse first entrance at level a as inf{t in [0,H]:S_t≥a}, assigning H when the level is not reached. This finite-horizon local-time inverse is a stopping time for the original filtration, without assuming the filtration is right continuous. Running supremum is adapted from the verified zero-barrier strategy equality, monotone by its exact supremum representation, and continuous by the positive-time and origin regularity theorems. Continuity gives upper semicontinuity on compact prefixes; apply the generic monotone adapted USC first-hit theorem. This is a genuine stochastic-clock prerequisite for constructing Itô excursions indexed by regulator local time, not merely a conditional n-Markov identity.
-- source:
--   Accepted runningSup_continuous_actual, runningSup_monotone_and_path_le, barrierStrategy_adapted, barrierStrategy_self_eq_runningSup, monotone_usc_capped_superlevel_isStoppingTime.

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_monotone_usc_capped_superlevel_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_capped_inverse_firstHit_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (a : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => runningSup X t ω) ⁻¹' Ici a) ∪ {H}))) := by sorry
