-- Prove2me | Theorems.Thm_ChvatalPosa_exists_nonadj_degree_sum
-- name    : ChvatalPosa.exists_nonadj_degree_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:18:32.196917+00:00
-- url     : https://prove2.me/theorems/3d15006b-67c7-5d11-9e47-0f5df2f3b01e
-- title:
--   Chvatal Posa: exists nonadj degree sum
-- statement:
--   Key step: under Chvátal's condition, a non-complete graph has two distinct non-adjacent
--   vertices whose degrees sum to at least `n`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L67-L137
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L67-L137

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]

theorem ChvatalPosa.exists_nonadj_degree_sum (H : SimpleGraph V) [DecidableRel H.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ChvatalCond H) (hnc : ∃ u v, u ≠ v ∧ ¬ H.Adj u v) :
    ∃ u v, u ≠ v ∧ ¬ H.Adj u v ∧ Fintype.card V ≤ H.degree u + H.degree v := by sorry
