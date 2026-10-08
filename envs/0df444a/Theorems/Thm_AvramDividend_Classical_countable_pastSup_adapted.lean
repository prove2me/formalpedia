-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted
-- name    : AvramDividend.Classical.countable_pastSup_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:25:43.856596+00:00
-- url     : https://prove2.me/theorems/c4b1ff1c-79f3-47aa-b695-38ca766f3a63
-- title:
--   Countably sampled running supremum of an adapted Levy process remains adapted
-- statement:
--   Let X be an adapted spectrally negative Levy process and let S be a countable subset of nonnegative observation times. The pathwise real running supremum of X_s over sampled times s in S no later than t is an adapted process: the index subtype is countable, each observation X_s is measurable in the sigma algebra at t by filtration monotonicity, and the supremum of countably many such measurable functions is measurable.
-- source:
--   Reusable measurability lemma for the Avram dividend strategy. Reducing the original continuous-time supremum to a rational-time representation is a separate mathematical obligation; this lemma does not falsely assume such a reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.countable_pastSup_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω) := by
  sorry
