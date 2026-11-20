-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_classTable_state
-- name    : Aggmetrics.DataStream.classTable_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:00:34.391397+00:00
-- url     : https://prove2.me/theorems/5955a0f8-6f74-4b75-88c1-d592b7984476
-- title:
--   Data Stream: class Table state
-- statement:
--   The temporal operator commutes with the selection matrices: the per-class table of the state
--   is the same weighted sum of the per-class tables of the instances.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L88-L90
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L88-L90

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.classTable_state {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (j : Fin m) :
    classTable (state w y p) j = ∑ k, w k • classTable (outer (y k) (p k)) j := by sorry
