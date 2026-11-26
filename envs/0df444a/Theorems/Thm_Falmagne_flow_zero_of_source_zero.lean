-- Prove2me | Theorems.Thm_Falmagne_flow_zero_of_source_zero
-- name    : Falmagne.flow_zero_of_source_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:32.740878+00:00
-- url     : https://prove2.me/theorems/ddc6372c-eff7-417c-8ea8-632e4c9e4013
-- title:
--   Falmagne: flow zero of source zero
-- statement:
--   The Falmagne construction uses the flow zero of source zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L22-L55
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L22-L55

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.flow_zero_of_source_zero (h : IsFlow q 0) : ∀ A x, x ∈ A → q x A = 0 := by sorry
