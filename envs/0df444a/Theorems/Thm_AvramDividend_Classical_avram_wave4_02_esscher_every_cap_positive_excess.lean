-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_every_cap_positive_excess
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_every_cap_positive_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:20:05.661039+00:00
-- url     : https://prove2.me/theorems/cc21af6e-7458-49c2-94e1-74cae648388c
-- title:
--   Every positive finite Esscher horizon has positive expected source local-time excess over any cap
-- statement:
--   For the actual spectrally negative Levy process with infinite small-jump first variation, the genuine Esscher law at every positive finite horizon has strictly positive expected positive part (S_t-b)^+ above any deterministic cap b and any real Esscher parameter theta. This source-specific result relies on source large-exponent growth and exact finite Esscher null-event equivalence; it constructs no excursion intensity.
-- source:
--   Theorem avram_wave4_02_source_localtime_every_cap_positive together with Proved finite Esscher null-event equivalence, genuine runningSup measurability and Mathlib lintegral_pos_iff_support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_localtime_every_cap_positive
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_null_events_iff
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_every_cap_positive_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) (b θ : ℝ) :
    0 < ∫⁻ ω, ENNReal.ofReal (runningSup X t ω - b)
      ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) := by sorry
