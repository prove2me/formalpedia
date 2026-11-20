-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_temporal_decomposability_matrix
-- name    : Aggmetrics.DataStream.temporal_decomposability_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:57:46.785179+00:00
-- url     : https://prove2.me/theorems/c454da9a-02af-4647-9668-468690464cde
-- title:
--   Data Stream: temporal decomposability matrix
-- statement:
--   **Dynamic Temporal Preservation of Linear Decomposability**, matrix form. For a nonnegative
--   state `C`, a measure `⟨a,v⟩/⟨b,v⟩` with `0 ≤ a ≤ b` and a positive pooled denominator, the measure
--   of the pooled per-class tables `∑ⱼ S_j C S_jᵀ` equals the denominator-weighted average of the
--   per-class measures; classes with a zero denominator get weight zero.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L194-L208
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L194-L208

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.temporal_decomposability_matrix {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable C j)) :
    measure a b (∑ j, classTable C j)
      = ∑ j, (lin b (classTable C j) / ∑ l, lin b (classTable C l))
          * measure a b (classTable C j) := by sorry
