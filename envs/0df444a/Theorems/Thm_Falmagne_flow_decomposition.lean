-- Prove2me | Theorems.Thm_Falmagne_flow_decomposition
-- name    : Falmagne.flow_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:34.568008+00:00
-- url     : https://prove2.me/theorems/1a5910ef-6fa0-53cf-80ac-3e550e9fee9c
-- title:
--   Falmagne: flow decomposition
-- statement:
--   Every nonnegative Boolean-lattice flow is a finite mixture of complete ranking paths.
--
--   This is proved by strong induction on the number of positive edges. Each step
--   subtracts the minimum edge weight of a positive complete path, annihilating
--   at least one edge. No flow decomposition theorem is assumed.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L174-L212
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean#L174-L212

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

theorem Falmagne.flow_decomposition [Nonempty X] (h : IsFlow q m) :
    ∃ μ : List X →₀ ℝ,
      (∀ l, 0 ≤ μ l) ∧
      (∀ l ∈ μ.support, l.Nodup ∧ l.toFinset = Finset.univ) ∧
      μ.sum (fun _ w => w) = m ∧
      (∀ x A, x ∈ A → μ.sum (fun l w => w * pathFlow l x A) = q x A) := by sorry
