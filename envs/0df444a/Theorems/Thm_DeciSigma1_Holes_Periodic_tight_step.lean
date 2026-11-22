-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_tight_step
-- name    : DeciSigma1.Holes.Periodic.tight_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:27.016801+00:00
-- url     : https://prove2.me/theorems/08f1db55-db35-4c0a-9707-468dade6cb45
-- title:
--   Periodic: tight step
-- statement:
--   Each tight constraint joins two pieces by a follower edge and increases the retained length
--   by less than `comparisonGap + statePeriodModulus`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L219-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L219-L238

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

theorem DeciSigma1.Holes.Periodic.tight_step (hM : 0 < statePeriodModulus N ρ.length)
    {P Q : {P // P ∈ piecesOf W ρ}} (ht : (shiftSystem W ρ N).IsTight z P Q) :
    FollowerEdge P.val Q.val ∧
      (Q.val.len : ℤ) + statePeriodModulus N ρ.length * z Q <
        (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P + comparisonGap N ρ.length +
            statePeriodModulus N ρ.length := by sorry
