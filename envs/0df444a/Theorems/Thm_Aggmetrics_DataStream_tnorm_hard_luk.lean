-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_tnorm_hard_luk
-- name    : Aggmetrics.DataStream.tnorm_hard_luk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:42.371112+00:00
-- url     : https://prove2.me/theorems/96ad7d7c-71a9-45cc-9ec9-76d915ba8b49
-- title:
--   Data Stream: tnorm hard luk
-- statement:
--   On a hard prediction the Łukasiewicz `t`-norm is the product.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L76-L80
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean#L76-L80

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.tnorm_hard_luk {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    max 0 (yt a + (if b = k then (1 : ℝ) else 0) - 1) = yt a * (if b = k then (1 : ℝ) else 0) := by sorry
