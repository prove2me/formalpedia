-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval
-- name    : AvramDividend.Classical.chat03_strict_lower_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:25:13.83766+00:00
-- url     : https://prove2.me/theorems/fb7f8fb8-daa2-49f9-ae6a-21b415fc40e5
-- title:
--   A strict downward Lévy crossing persists throughout a nonempty right interval
-- statement:
--   For an official spectrally negative Lévy process and any sample path, when its value is strictly below a real lower threshold at t, there is a concrete u>t such that the value stays strictly below that threshold for every s in [t,u). This is the lower-side companion of the previously Proved strict upper passage persistence theorem. It uses only the process sample-path right-continuity, enabling horizon-preserving grid approximation of lower strict passages.
-- source:
--   Official SpectrallyNegativeLevy.rightCont and pinned Mathlib right-neighbourhood interval basis.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_lower_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower : ℝ)
    (h : X.X t ω < lower) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → X.X s ω < lower := by sorry
