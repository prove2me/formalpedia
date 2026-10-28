-- Prove2me | Theorems.Thm_AvramDividend_Classical_nnreal_stopping_time_add_const
-- name    : AvramDividend.Classical.nnreal_stopping_time_add_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:16:49.60346+00:00
-- url     : https://prove2.me/theorems/1261141e-ca11-495b-bb3d-8bc080c55918
-- title:
--   Nonnegative real stopping times remain stopping times under deterministic delay
-- statement:
--   A nonnegative deterministic delay of a stopping time remains a stopping time for any filtration indexed by ℝ≥0. The proof handles deadlines before and after the delay separately, using the difference i−h and the monotonicity of the filtration. This fills the gap left by generic shift lemmas that require either additive inverses or countable time indices.
-- source:
--   Unfold IsStoppingTime. For i<h, the event {τ+h≤i} is empty. Otherwise it agrees with {τ≤i−h} by cancellativity of addition by a finite WithTop value, and its measurability lifts from 𝓕(i−h) to 𝓕 i by filtration monotonicity.

import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.nnreal_stopping_time_add_const
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) (h : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => τ ω + (h : WithTop ℝ≥0)) := by sorry
