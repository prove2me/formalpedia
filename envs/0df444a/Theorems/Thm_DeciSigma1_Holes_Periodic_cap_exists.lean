-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_cap_exists
-- name    : DeciSigma1.Holes.Periodic.cap_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:38.264652+00:00
-- url     : https://prove2.me/theorems/0871aba0-2f3c-490c-972d-b9e2db767962
-- title:
--   Periodic: cap exists
-- statement:
--   There is an admissible deletion after which every piece of the class has at most
--   `pieceLengthBound N |ρ| h t` letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L360-L408
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L360-L408

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

theorem DeciSigma1.Holes.Periodic.cap_exists (N : ℕ) {h t : ℕ} (hρ : IsPrimitive ρ)
    (split : OccurrenceSplit W ρ h t) :
    ∃ x, AdmissibleDeletion W ρ N x ∧
      ∀ P ∈ piecesOf W ρ, P.len - statePeriodModulus N ρ.length * x P ≤
          pieceLengthBound N ρ.length h t := by sorry
