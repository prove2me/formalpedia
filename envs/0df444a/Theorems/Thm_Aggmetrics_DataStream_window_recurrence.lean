-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_window_recurrence
-- name    : Aggmetrics.DataStream.window_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:09.142185+00:00
-- url     : https://prove2.me/theorems/3f12869b-7f65-4798-abbe-688bf5ccc52a
-- title:
--   Data Stream: window recurrence
-- statement:
--   The window recurrence `C(n+1) = C(n) + (1/W)(y_n p_nᵀ - y_{n-W} p_{n-W}ᵀ)`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L297-L323
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L297-L323

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.window_recurrence {m : ℕ} {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) (y p : ℕ → Fin m → ℝ) :
    winState W y p (n + 1)
      = winState W y p n + (1 / (W : ℝ)) • (outer (y n) (p n) - outer (y (n - W)) (p (n - W))) := by sorry
