-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_floor_edit
-- name    : DeciSigma1.Holes.Periodic.floor_edit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:15.416795+00:00
-- url     : https://prove2.me/theorems/6f7f83e8-017c-4fdd-832a-9bc2c40d287c
-- title:
--   Periodic: floor edit
-- statement:
--   A nonpositive shift `z` at or above the floor `-((L - F) / M)` deletes at most `L` letters,
--   nothing from a piece shorter than `F`, and otherwise leaves at least `F` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L101-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L101-L120

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

theorem DeciSigma1.Holes.Periodic.floor_edit {L F M : ℕ} {z : ℤ}
    (hz : -(((L - F) / M : ℕ) : ℤ) ≤ z) (hz0 : z ≤ 0) :
    M * (-z).toNat ≤ L ∧ (L < F → (-z).toNat = 0) ∧
      ((-z).toNat ≠ 0 → F + M * (-z).toNat ≤ L) := by sorry
