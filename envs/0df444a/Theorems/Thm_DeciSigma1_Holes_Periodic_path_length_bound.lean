-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_path_length_bound
-- name    : DeciSigma1.Holes.Periodic.path_length_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:35.735518+00:00
-- url     : https://prove2.me/theorems/0e843e4c-cd6c-423a-9d44-88b79c58db78
-- title:
--   Periodic: path length bound
-- statement:
--   If each step of a path increases `v` by at most `B`, the whole path increases `v` by at most
--   its number of steps times `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L343-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L343-L356

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
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}

theorem DeciSigma1.Holes.Periodic.path_length_bound {ι : Type} (v : ι → ℤ) (B : ℤ) (r : ι → ι → Prop)
    (hstep : ∀ i j, r i j → v j ≤ v i + B) :
    ∀ (i : ι) (p : List ι), (i :: p).IsChain r →
      v ((i :: p).getLast (List.cons_ne_nil _ _)) ≤ v i + p.length * B := by sorry
