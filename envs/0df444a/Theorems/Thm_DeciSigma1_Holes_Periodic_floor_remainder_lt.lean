-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_floor_remainder_lt
-- name    : DeciSigma1.Holes.Periodic.floor_remainder_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:16.345798+00:00
-- url     : https://prove2.me/theorems/7b0c3978-e3b3-46d8-bd29-97e0d506557a
-- title:
--   Periodic: floor remainder lt
-- statement:
--   At the floor, fewer than `F + M` letters remain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L123-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L123-L136

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

theorem DeciSigma1.Holes.Periodic.floor_remainder_lt {L F M : ℕ} (hM : 0 < M) :
    (L : ℤ) + (M : ℤ) * (-(((L - F) / M : ℕ) : ℤ)) < (F : ℤ) + M := by sorry
