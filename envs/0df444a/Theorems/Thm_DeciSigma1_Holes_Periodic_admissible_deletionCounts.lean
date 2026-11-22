-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_admissible_deletionCounts
-- name    : DeciSigma1.Holes.Periodic.admissible_deletionCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:25.676682+00:00
-- url     : https://prove2.me/theorems/ef3580e5-94fb-4d50-8929-3135e71ada8b
-- title:
--   Periodic: admissible deletion Counts
-- statement:
--   Every nonpositive solution above the floors gives an admissible deletion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L186-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L186-L215

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

theorem DeciSigma1.Holes.Periodic.admissible_deletionCounts (hs : (shiftSystem W ρ N).Sat z)
    (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (hM : 0 < statePeriodModulus N ρ.length) : AdmissibleDeletion W ρ N (deletionCounts z) := by sorry
