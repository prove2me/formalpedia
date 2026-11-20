-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_bias_identity
-- name    : Aggmetrics.DataStream.bias_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:46.768786+00:00
-- url     : https://prove2.me/theorems/759b5640-3e9c-4470-befa-bc18c6af54a0
-- title:
--   Data Stream: bias identity
-- statement:
--   `C_oracle - C = ∑ₖ (1 - Oₖ) wₖ (yₖ - ỹₖ) pₖᵀ`, exactly.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L91-L98
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L91-L98

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.bias_identity {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ) :
    state w y p - unified w O y yt p
      = ∑ k, ((1 - O k) * w k) • outer (fun c => y k c - yt k c) (p k) := by sorry
