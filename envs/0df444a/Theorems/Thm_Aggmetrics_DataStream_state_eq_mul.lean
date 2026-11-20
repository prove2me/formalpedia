-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_state_eq_mul
-- name    : Aggmetrics.DataStream.state_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:46.669533+00:00
-- url     : https://prove2.me/theorems/d8dcb77e-25ff-4359-956b-74ea6ef22fa9
-- title:
--   Data Stream: state eq mul
-- statement:
--   `C = Yᵀ W P` as a matrix product.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L63-L66
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L63-L66

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.state_eq_mul {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) :
    state w y p = (Matrix.of y)ᵀ * Matrix.diagonal w * Matrix.of p := by sorry
