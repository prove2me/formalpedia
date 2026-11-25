-- Prove2me | Theorems.Thm_CliqueMinors_DiracCtx_op
-- name    : CliqueMinors.DiracCtx.op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:39:45.315139+00:00
-- url     : https://prove2.me/theorems/062a8550-b53f-429d-bcc9-6df84d2ed4bb
-- title:
--   Dirac Ctx: op
-- statement:
--   The Dirac Ctx construction uses the op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L342-L411
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L342-L411

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

theorem CliqueMinors.DiracCtx.op (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) (hac' : a ≠ c)
    (ha4 : 4 ≤ G.degree a) (hc4 : 4 ≤ G.degree c) : False := by sorry
