-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_retained_cast
-- name    : DeciSigma1.Holes.Periodic.retained_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:18.022935+00:00
-- url     : https://prove2.me/theorems/dc92298b-6b50-47cb-af2c-b117f9f89bef
-- title:
--   Periodic: retained cast
-- statement:
--   Retained natural lengths agree with the signed length formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L175-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L175-L183

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

theorem DeciSigma1.Holes.Periodic.retained_cast (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (P : {P // P ∈ piecesOf W ρ}) :
    ((P.val.len - statePeriodModulus N ρ.length * deletionCounts z P.val : ℕ) : ℤ) =
      (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P := by sorry
