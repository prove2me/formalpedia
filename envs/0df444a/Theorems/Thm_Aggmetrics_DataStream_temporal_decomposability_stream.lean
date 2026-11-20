-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_temporal_decomposability_stream
-- name    : Aggmetrics.DataStream.temporal_decomposability_stream
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:25.272947+00:00
-- url     : https://prove2.me/theorems/56e97f3c-4e6d-4b4a-aedf-42a98818914d
-- title:
--   Data Stream: temporal decomposability stream
-- statement:
--   The same for the temporal state `Yᵀ W P` of a stream, for **any** nonnegative weighting `w`
--   and nonnegative label and prediction vectors.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L212-L219
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L212-L219

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.temporal_decomposability_stream {m n : ℕ} (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (y p : Fin n → Fin m → ℝ) (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable (state w y p) j)) :
    measure a b (∑ j, classTable (state w y p) j)
      = ∑ j, (lin b (classTable (state w y p) j) / ∑ l, lin b (classTable (state w y p) l))
          * measure a b (classTable (state w y p) j) := by sorry
