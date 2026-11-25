-- Prove2me | Theorems.Thm_CliqueMinors_DiracCtx_card_nbr
-- name    : CliqueMinors.DiracCtx.card_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:34.676088+00:00
-- url     : https://prove2.me/theorems/41171894-884a-4bbf-a5f3-67a09d33f814
-- title:
--   Dirac Ctx: card nbr
-- statement:
--   The Dirac Ctx construction uses the card nbr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L327-L329
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L327-L329

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}

theorem CliqueMinors.DiracCtx.card_nbr (H : DiracCtx G S) {v w : V} (h : G.Adj v w) :
    3 ≤ (G.neighborFinset v).card := by sorry
