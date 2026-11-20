-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_discrete_decomposition
-- name    : Aggmetrics.DataStream.discrete_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:59:30.174195+00:00
-- url     : https://prove2.me/theorems/790db963-3c24-4648-a32b-8bad72cb9188
-- title:
--   Data Stream: discrete decomposition
-- statement:
--   Exact discrete product rule: `Δ(ωM) = ω̄ ΔM + Δω M̄` with mid-point values.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L328-L333
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L328-L333

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.discrete_decomposition {m : ℕ} (ω0 ω1 M0 M1 : Fin m → ℝ) :
    ∑ j, (ω1 j * M1 j - ω0 j * M0 j)
      = ∑ j, ((ω0 j + ω1 j) / 2) * (M1 j - M0 j)
        + ∑ j, (ω1 j - ω0 j) * ((M0 j + M1 j) / 2) := by sorry
