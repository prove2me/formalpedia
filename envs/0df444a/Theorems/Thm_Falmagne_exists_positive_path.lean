-- Prove2me | Theorems.Thm_Falmagne_exists_positive_path
-- name    : Falmagne.exists_positive_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:33.687264+00:00
-- url     : https://prove2.me/theorems/bcf34c1a-2a64-43f0-970e-18bec0b72cdb
-- title:
--   Falmagne: exists positive path
-- statement:
--   A positive outgoing flow extends to a positive complete elimination path.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L58-L103
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L58-L103

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.exists_positive_path (h : IsFlow q m) (A : Finset X) (hpos : 0 < outflow q A) :
    ∃ l : List X, l.Nodup ∧ l.toFinset = A ∧
      ∀ x B, pathFlow l x B ≠ 0 → 0 < q x B := by sorry
