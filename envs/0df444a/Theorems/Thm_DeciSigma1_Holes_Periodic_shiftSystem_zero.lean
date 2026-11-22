-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_shiftSystem_zero
-- name    : DeciSigma1.Holes.Periodic.shiftSystem_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:13.17109+00:00
-- url     : https://prove2.me/theorems/4ed5a1e9-4d6b-4ff3-a17c-62cfd834dbe1
-- title:
--   Periodic: shift System zero
-- statement:
--   The zero shift, which deletes nothing, solves the system.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L74-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L74-L81

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}

theorem DeciSigma1.Holes.Periodic.shiftSystem_zero (N : ℕ) : (shiftSystem W ρ N).Sat (fun _ => 0) := by sorry
