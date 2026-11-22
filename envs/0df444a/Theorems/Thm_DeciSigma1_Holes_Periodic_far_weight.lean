-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_far_weight
-- name    : DeciSigma1.Holes.Periodic.far_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:20.073073+00:00
-- url     : https://prove2.me/theorems/da75890b-874d-4c56-8f42-992abcf72f9c
-- title:
--   Periodic: far weight
-- statement:
--   A constraint between pieces of lengths `L + K ≤ Q` keeps the gap: the edited lengths satisfy
--   `L + M a + K ≤ Q + M b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L140-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L140-L149

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

theorem DeciSigma1.Holes.Periodic.far_weight {L Q K M : ℕ} {a b : ℤ} (hM : 0 < M) (hfar : L + K ≤ Q)
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) ≤ b) :
    (L : ℤ) + M * a + K ≤ (Q : ℤ) + M * b := by sorry
