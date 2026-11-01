-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_localtime_positive_exposure
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_localtime_positive_exposure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:23:38.791435+00:00
-- url     : https://prove2.me/theorems/683026cf-d8d0-412a-a842-da4ac1b80778
-- title:
--   Strictly positive true finite Esscher running-local-time exposure
-- statement:
--   Under the actual positive-root terminal Esscher measure at time one, the expected true running supremum is strictly positive in ENNReal. This identifies the nondegenerate local-time normaliser for finite-clock reflected-excursion compensation from the source Lévy process, using the proved source positive-mass event, finite Esscher null-event equivalence and measurability of the genuine running supremum.
-- source:
--   Canonically Proved chat04_esscher_finite_horizon_null_events_iff (abd6d3fb) and levy_runningSup_joint_time_path_measurable (ecfe330c), plus source-root positive mass child 7f2aee5e once accepted; Mathlib lintegral_pos_iff_support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_true_localtime_positive_mass
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_null_events_iff
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_localtime_positive_exposure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 < ∫⁻ ω, ENNReal.ofReal (runningSup X (1 : ℝ≥0) ω)
      ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))) := by sorry
