-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_far_tight
-- name    : DeciSigma1.Holes.Periodic.far_tight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:16.702789+00:00
-- url     : https://prove2.me/theorems/179e3b19-b5e0-4c10-a2f2-184760eb2d86
-- title:
--   Periodic: far tight
-- statement:
--   Along a tight constraint between pieces of lengths `L + K ≤ Q`, the edited length increases by
--   less than `K + M`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L153-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L153-L163

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

theorem DeciSigma1.Holes.Periodic.far_tight {L Q K M : ℕ} {a b : ℤ} (hM : 0 < M) (hfar : L + K ≤ Q)
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) = b) :
    (Q : ℤ) + M * b < (L : ℤ) + M * a + K + M := by sorry
