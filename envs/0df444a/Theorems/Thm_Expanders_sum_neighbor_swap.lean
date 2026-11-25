-- Prove2me | Theorems.Thm_Expanders_sum_neighbor_swap
-- name    : Expanders.sum_neighbor_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:08:37.884964+00:00
-- url     : https://prove2.me/theorems/f4917c2a-6da4-5c17-b634-465bcb280e4d
-- title:
--   Expanders: sum neighbor swap
-- statement:
--   The Expanders construction uses the sum neighbor swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L66-L74
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L66-L74

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.sum_neighbor_swap (G : SimpleGraph V) [DecidableRel G.Adj] (F : V → V → ℝ) :
    ∑ v, ∑ w ∈ G.neighborFinset v, F v w = ∑ v, ∑ w ∈ G.neighborFinset v, F w v := by sorry
