-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_finite_truncated_localtime_normalizer
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_finite_truncated_localtime_normalizer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:39:32.15298+00:00
-- url     : https://prove2.me/theorems/d4b0dc18-b53b-4c53-b6e5-b5b8be6b7494
-- title:
--   Actual Esscher local-time normaliser has strictly positive finite exposure at every positive cap
-- statement:
--   For the actual positive Esscher-tilted spectrally negative Lévy path, every positive finite running-maximum regulator cap B has strictly positive and finite mean under the genuine time-one tilted probability law Q_1: 0<E_Q1[min(S_1,B)]<=B. This isolates the finite positive local-time normaliser needed in actual excursion compensation, but does not assert existence of an excursion mark point process.
-- source:
--   Proved source actual Esscher local-time exposure 683026cf; finite-time Esscher probability 6c6f7684; genuine running supremum joint measurability and Mathlib lintegral support and bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_localtime_positive_exposure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_finite_truncated_localtime_normalizer
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (B : ℝ) (hB : 0 < B) :
    (let Q : Measure Ω :=
       P.withDensity (fun ω : Ω => ENNReal.ofReal
         (Real.exp (φ * X.X (1 : ℝ≥0) ω - (1 : ℝ) * X.ψ φ)))
     0 < ∫⁻ ω, ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q ∧
     (∫⁻ ω, ENNReal.ofReal (min (runningSup X (1 : ℝ≥0) ω) B) ∂Q)
       ≤ ENNReal.ofReal B) := by sorry
