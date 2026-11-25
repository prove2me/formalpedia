-- Prove2me | Theorems.Thm_Expanders_exists_adj_dist_lt
-- name    : Expanders.exists_adj_dist_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:08:50.3148+00:00
-- url     : https://prove2.me/theorems/e79accec-dafb-487c-ba76-40aa350943fb
-- title:
--   Expanders: exists adj dist lt
-- statement:
--   The Expanders construction uses the exists adj dist lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L41-L51
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L41-L51

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} {G : SimpleGraph V}

theorem Expanders.exists_adj_dist_lt {u v : V} (huv : G.Reachable u v) (h0 : G.dist u v ≠ 0) :
    ∃ w, G.Adj v w ∧ G.Reachable u w ∧ G.dist u w + 1 ≤ G.dist u v := by sorry
