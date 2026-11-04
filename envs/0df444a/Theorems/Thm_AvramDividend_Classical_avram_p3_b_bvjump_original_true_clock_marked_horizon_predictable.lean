-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_true_clock_marked_horizon_predictable
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_marked_horizon_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:02.443647+00:00
-- url     : https://prove2.me/theorems/b47ffa25-8286-423c-8c06-fdcbee65dff3
-- title:
--   Genuine right-continuous predictable marked horizon set is measurable
-- statement:
--   Under the original right-continuous filtration, the exact finite-horizon set {((u,ω),z) | u≤T} is measurable in the genuine predictable time-path sigma algebra paired with the original mark Borel space. Derive this from Mathlib's predictable zero-time and (0,T] cylinders. This discharges the hS measurable stopped-source support premise in the accepted original BV signed L1 compensation theorem, requiring no P2 source jump-rate hypothesis or new process.
-- source:
--   Mathlib.Probability.Process.Predictable measurableSet_predictable_singleton_bot_prod and measurableSet_predictable_Ioc_prod; original accepted 4846bbef hS

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_marked_horizon_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by sorry
