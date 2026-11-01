-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonjump_iff_continuous_at
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_source_nonjump_iff_continuous_at
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:33:36.827543+00:00
-- url     : https://prove2.me/theorems/d98a57fe-9efb-4d48-9ba0-99985f8fa52e
-- title:
--   An original source Lévy path is continuous at a positive time exactly when its actual jump mark vanishes
-- statement:
--   For the original spectrally negative Lévy X, without a BV or finite-intensity hypothesis, a positive time is a continuity point of the genuine sample X(·,ω) exactly if its actual left-limit jump mark is zero. This combines the X.leftLim and X.rightCont fields on the unchanged probability space. It is a source càdlàg discontinuity/jump identification required to transfer a jump-free interval into continuity and then derive finite-activity grid/count matching; no constructed replacement or stochastic compensator is claimed.
-- source:
--   Pinned source SpectrallyNegativeLevy.leftLim and SpectrallyNegativeLevy.rightCont; pinned Mathlib ContinuousWithinAt.union, continuousWithinAt_univ, leftLim_eq_of_tendsto. The left and right half-lines cover the time domain; continuity from the left at nonjump t plus original right continuity is ordinary continuity. Conversely ordinary continuity fixes the left limit. This source-path fact is a necessary exact pathwise step toward the actual jump count law.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_source_nonjump_iff_continuous_at
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    X.X t ω -
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = 0 ↔
      ContinuousAt (fun u : ℝ≥0 => X.X u ω) t := by sorry
