-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_micro_change_decomposition
-- name    : Aggmetrics.DataStream.micro_change_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:20.070342+00:00
-- url     : https://prove2.me/theorems/175f6df7-a531-45a1-b738-e163d8fe68db
-- title:
--   Data Stream: micro change decomposition
-- statement:
--   The change of the pooled measure between two states splits into an intrinsic part (change of
--   the per-class measures, mid-point weights) and a prevalence part (change of the weights, mid-point
--   measures), exactly. This is Eq. `drift_decomposition` of the paper.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L342-L354
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamTemporal.lean#L342-L354

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.micro_change_decomposition {m : ℕ} (C0 C1 : Matrix (Fin m) (Fin m) ℝ)
    (hC0 : ∀ a b, 0 ≤ C0 a b) (hC1 : ∀ a b, 0 ≤ C1 a b)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos0 : 0 < ∑ j, lin b (classTable C0 j)) (hpos1 : 0 < ∑ j, lin b (classTable C1 j)) :
    measure a b (∑ j, classTable C1 j) - measure a b (∑ j, classTable C0 j)
      = ∑ j, ((omega b C0 j + omega b C1 j) / 2)
            * (measure a b (classTable C1 j) - measure a b (classTable C0 j))
        + ∑ j, (omega b C1 j - omega b C0 j)
            * ((measure a b (classTable C0 j) + measure a b (classTable C1 j)) / 2) := by sorry
