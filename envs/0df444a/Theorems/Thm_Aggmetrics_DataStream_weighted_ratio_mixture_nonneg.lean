-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_weighted_ratio_mixture_nonneg
-- name    : Aggmetrics.DataStream.weighted_ratio_mixture_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:58:47.086987+00:00
-- url     : https://prove2.me/theorems/62eeac90-78f9-4699-840b-47db82c7327d
-- title:
--   Data Stream: weighted ratio mixture nonneg
-- statement:
--   Generalization of `weighted_ratio_mixture`: classes whose denominator is zero are allowed, if
--   their numerator is zero too, and then carry weight zero.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L37-L45
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L37-L45

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.weighted_ratio_mixture_nonneg {m : ℕ} (num den : Fin m → ℝ)
    (hnum : ∀ j, den j = 0 → num j = 0) (hpos : 0 < ∑ j, den j) :
    (∑ j, num j) / (∑ j, den j)
      = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by sorry
