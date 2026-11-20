-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_row_prior_invariant
-- name    : Aggmetrics.DataStream.row_prior_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:51.586176+00:00
-- url     : https://prove2.me/theorems/afc2f0cf-02d2-4ea3-9cdf-9d138d2e2a83
-- title:
--   Data Stream: row prior invariant
-- statement:
--   The rows of the confusion matrix do not depend on the prior: normalizing the joint cells
--   `π_k c_{kl}` of a class with `π_k ≠ 0` gives back `c_{kl}`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L182-L186
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L182-L186

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.row_prior_invariant {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ)
    (hrow : ∀ k, ∑ l, c k l = 1) (k l : Fin m) (hπ : π k ≠ 0) :
    (π k * c k l) / (∑ l', π k * c k l') = c k l := by sorry
