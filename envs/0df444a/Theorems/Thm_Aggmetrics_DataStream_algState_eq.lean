-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_algState_eq
-- name    : Aggmetrics.DataStream.algState_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:40.227979+00:00
-- url     : https://prove2.me/theorems/10313512-a642-43fd-8a6a-2acdb2d3705c
-- title:
--   Data Stream: alg State eq
-- statement:
--   **Invariant of Algorithm 1.** If every label arrives after its instance (`k < arr k`), the
--   running matrix after `n` steps is the unified state `∑ₖ w_k(n) ỹ-or-y_k p_kᵀ` with the fading
--   weights, in which a label that has arrived has replaced its stand-in.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L173-L230
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L173-L230

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
open scoped Classical

theorem Aggmetrics.DataStream.algState_eq {m : ℕ} (α : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n
      = ∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k) := by sorry
