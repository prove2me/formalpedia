-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_generic_usc_fullPrefixSup_adapted
-- name    : AvramDividend.Classical.avram_gbB31_generic_usc_fullPrefixSup_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:56:39.105461+00:00
-- url     : https://prove2.me/theorems/86436f68-bbe6-4c4a-b7ef-d6910b318a9c
-- title:
--   Generic upper semicontinuous right-continuous process full prefix supremum adapted
-- statement:
--   For any filtration-adapted real-valued right-continuous process whose paths are upper semicontinuous on every compact nonnegative interval, prove its full prefix supremum is adapted, using a countable dense time set plus the right endpoint. This extracts the generic sound argument used in the proved reflected supremum construction, enabling stopped risk-process cutoff clocks.

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_generic_usc_fullPrefixSup_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (U : ℝ≥0 → Ω → ℝ) (hAdapt : Adapted 𝓕 U)
    (hRight : ∀ ω (u : ℝ≥0),
      ContinuousWithinAt (fun t => U t ω) (Ici u) u)
    (hUSC : ∀ ω (t : ℝ≥0),
      UpperSemicontinuousOn (fun u => U u ω) (Icc 0 t))
    (S : Set ℝ≥0) (hS : S.Countable)
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : Set.Icc (0 : ℝ≥0) t, U s.1 ω) := by sorry
