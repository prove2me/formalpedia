-- Prove2me | Theorems.Thm_Falmagne_flow_subtract_path
-- name    : Falmagne.flow_subtract_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:28.984319+00:00
-- url     : https://prove2.me/theorems/071c1b51-d12f-5b09-a5ed-552a705b9b62
-- title:
--   Falmagne: flow subtract path
-- statement:
--   Remove a positive complete unit path at its smallest edge weight.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L113-L166
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L113-L166

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.flow_subtract_path [Nonempty X] (h : IsFlow q m) (hm : 0 < m) :
    ∃ (l : List X) (δ : ℝ), l.Nodup ∧ l.toFinset = Finset.univ ∧ 0 < δ ∧
      IsFlow (fun x A => q x A - δ * pathFlow l x A) (m - δ) ∧
      (edgeSupport (fun x A => q x A - δ * pathFlow l x A)).card < (edgeSupport q).card := by sorry
