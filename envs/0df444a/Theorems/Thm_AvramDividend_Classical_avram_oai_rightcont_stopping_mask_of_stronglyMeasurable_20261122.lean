-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
-- name    : AvramDividend.Classical.avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:16:31.364415+00:00
-- url     : https://prove2.me/theorems/54d9e03e-0de0-49f0-a73a-7946d20ae498
-- title:
--   Actual right-continuous stopping-time survival mask preserves predictability of a pre-stop measurable real grid weight
-- statement:
--   For any original ℝ≥0-time filtration ℱ, genuine stopping time τ with respect to ℱ.rightCont, deterministic grid start t and real H strongly measurable in ℱ.rightCont t, prove the stop-survival masked predictor ω↦if τω≤t then 0 else Hω remains StronglyMeasurable[ℱ.rightCont t]. This is the exact stopped predictable mask needed to apply proved all-activity original physical signed simple marked jump future conditional centring to stopped positive-clock Itô–Meyer grids. Proof uses the REAL stopping-time definition measurableSet[ℱ.rightCont t] {τω≤t}, and pinned stronglyMeasurable.ite; no synthetic stopped process or extra filtration assumption.

import Mathlib
open MeasureTheory
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (t : ℝ≥0) (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont t] H) :
    StronglyMeasurable[𝓕.rightCont t]
      (fun ω => if τ ω ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else H ω) := by sorry
