-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_actual_cap_source_generator_HJB_nonpos
-- name    : AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generator_HJB_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:59:45.620433+00:00
-- url     : https://prove2.me/theorems/e3eed1c6-33a4-45a1-ab21-abca1d4f5ddc
-- title:
--   Actual original spectrally negative Lévy HJB generator sign transfers to cap continuation on strict interior
-- statement:
--   For the same original spectrally negative Lévy process, the full source generator of the slope-one cap continuation V has the same value as w on strict interior reserves, and V=w there. Thus X.generator V - q*V≤0 follows from the source candidate HJB sign without changing processes, equality in law, or assuming global smoothness at the cap. This supplies the drift sign for the P3 physical finite grid instantiated with V.
-- source:
--   Proved avram_wave4_04_cap_linear_extension_source_generator_eq_interior; exact cap equations and pinned ENNReal finite-cap conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generator_HJB_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (q : ℝ)
    (hw_gen : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.generator w z - q * w z ≤ 0) :
    ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.generator V z - q * V z ≤ 0 := by sorry
