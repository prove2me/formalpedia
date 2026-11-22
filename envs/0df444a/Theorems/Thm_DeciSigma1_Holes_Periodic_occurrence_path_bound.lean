-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_occurrence_path_bound
-- name    : DeciSigma1.Holes.Periodic.occurrence_path_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:34.791835+00:00
-- url     : https://prove2.me/theorems/ae86ac0e-9446-4d6a-a30b-4180efe1d7ab
-- title:
--   Periodic: occurrence path bound
-- statement:
--   A simple follower path with head height `h` and at most `t` tails has at most
--   `(t + 1) * 2 ^ h - 1` vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L299-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L299-L339

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

theorem DeciSigma1.Holes.Periodic.occurrence_path_bound {h t : ℕ} (split : OccurrenceSplit W ρ h t)
    (p : List {P // P ∈ piecesOf W ρ}) (hnd : p.Nodup)
    (hp : p.IsChain (fun P Q => FollowerEdge P.val Q.val)) :
    p.length ≤ (t + 1) * 2 ^ h - 1 := by sorry
