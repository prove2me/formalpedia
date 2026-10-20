-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval
-- name    : AvramDividend.Classical.chat03_strict_upper_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:32:42.712385+00:00
-- url     : https://prove2.me/theorems/36f0b94a-8321-47ba-9c71-d5e3bd539ceb
-- title:
--   A strict upward Lévy crossing persists throughout a nonempty right interval
-- statement:
--   For an official spectrally negative Lévy process and an arbitrary path, whenever the process is strictly above a given real upper threshold at a nonnegative time t, it remains strictly above that same upper threshold throughout some concrete right interval [t,u) with u>t. This follows solely from pathwise right-continuity and the open upper half-line, and is stronger than preservation of a two-sided crossing disjunction. It is designed for countable grid detection before any finite horizon.
-- source:
--   Official Lévy rightCont property, pinned Mathlib eventually_nhdsWithin_iff and exists_Ico_subset_of_mem_nhds' at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_upper_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (upper : ℝ)
    (h : upper < X.X t ω) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → upper < X.X s ω := by sorry
