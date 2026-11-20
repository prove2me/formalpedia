-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_lost_entry
-- name    : Aggmetrics.DataStream.lost_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:05.041877+00:00
-- url     : https://prove2.me/theorems/97ff2ac4-a1f9-4240-9f05-539b19415a14
-- title:
--   Data Stream: lost entry
-- statement:
--   The Data Stream construction uses the lost entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L302-L314
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean#L302-L314

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.lost_entry {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (n : ℕ) (a b : Fin m) :
    (lostState α ε y yt p aud arr n) a b
      = ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k),
          fadeWeight α n k * ((y k a - yt k a) * p k b) := by sorry
