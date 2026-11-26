-- Prove2me | Theorems.Thm_Falmagne_flow_edge_le_outflow
-- name    : Falmagne.flow_edge_le_outflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:29.114318+00:00
-- url     : https://prove2.me/theorems/9b5a34ab-a49c-524f-b2ae-ab09d5b7bb22
-- title:
--   Falmagne: flow edge le outflow
-- statement:
--   The Falmagne construction uses the flow edge le outflow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L14-L15
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L14-L15

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.flow_edge_le_outflow (h : IsFlow q m) (hx : x ∈ A) : q x A ≤ outflow q A := by sorry
