-- Prove2me | Theorems.Thm_CliqueMinors_DiracCtx_deg_four
-- name    : CliqueMinors.DiracCtx.deg_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:11.304992+00:00
-- url     : https://prove2.me/theorems/d4d90a63-cc3a-4355-a990-ce08f67b42d8
-- title:
--   Dirac Ctx: deg four
-- statement:
--   The Dirac Ctx construction uses the deg four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L435-L471
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L435-L471

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

theorem CliqueMinors.DiracCtx.deg_four (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hac : ¬ G.Adj a c) : 4 ≤ G.degree a := by sorry
