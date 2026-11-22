-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_least_shifts
-- name    : DeciSigma1.Holes.Periodic.least_shifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:13.179517+00:00
-- url     : https://prove2.me/theorems/9d8a4156-6aa9-4f70-bca0-86bbb2eb39a5
-- title:
--   Periodic: least shifts
-- statement:
--   The least solution above the floors: it is nonpositive, and every piece is reached by a
--   duplicate-free path of tight constraints from a piece at its floor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L85-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L85-L97

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

theorem DeciSigma1.Holes.Periodic.least_shifts (N : ℕ) :
    ∃ z : {P // P ∈ piecesOf W ρ} → ℤ,
      (shiftSystem W ρ N).Sat z ∧ (∀ P, shiftFloor N P.val ≤ z P) ∧
      (∀ y, (shiftSystem W ρ N).Sat y → (∀ P, shiftFloor N P.val ≤ y P) → z ≤ y) ∧
      (∀ P, z P ≤ 0) ∧
      ∀ P, ∃ p : List {P // P ∈ piecesOf W ρ}, p.Nodup ∧ p.getLast? = some P ∧
        (∃ Q, p.head? = some Q ∧ z Q = shiftFloor N Q.val) ∧
        p.IsChain ((shiftSystem W ρ N).IsTight z) := by sorry
