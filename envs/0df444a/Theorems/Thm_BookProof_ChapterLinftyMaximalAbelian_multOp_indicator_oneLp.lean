-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_multOp_indicator_oneLp
-- name    : BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:43.67145+00:00
-- url     : https://prove2.me/theorems/e921a04c-82bd-40ed-b804-97b18e668598
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp` {s : Set α} (hs : MeasurableSet s) (c : ℂ) : multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneL
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp` {s : Set α} (hs : MeasurableSet s) (c : ℂ) : multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ) = indicatorConstLp 2 hs (measure_ne_top μ s) c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp {s : Set α} (hs : MeasurableSet s) (c : ℂ) :
    multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ)
      = indicatorConstLp 2 hs (measure_ne_top μ s) c := by sorry
