-- Prove2me | Theorems.Thm_Falmagne_mem_edgeSupport
-- name    : Falmagne.mem_edgeSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:25.156396+00:00
-- url     : https://prove2.me/theorems/c61dc3f3-2901-5cb2-8064-f7427eedb948
-- title:
--   Falmagne: mem edge Support
-- statement:
--   The Falmagne construction uses the mem edge Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L108-L110
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L108-L110

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.mem_edgeSupport (q : X → Finset X → ℝ) (e : X × Finset X) :
    e ∈ edgeSupport q ↔ e.1 ∈ e.2 ∧ 0 < q e.1 e.2 := by sorry
