-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_simplePath_le_pow_split
-- name    : DeciSigma1.Holes.Periodic.simplePath_le_pow_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:36.98603+00:00
-- url     : https://prove2.me/theorems/af223aca-d94b-40c1-9835-82378ca48e3e
-- title:
--   Periodic: simple Path le pow split
-- statement:
--   A prefix-comparability path is bounded by its number of tails and the comparable height
--   of its heads.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L242-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Bound.lean#L242-L285

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

theorem DeciSigma1.Holes.Periodic.simplePath_le_pow_split {β γ : Type*} (f : β → List γ) (head : β → Prop)
    [DecidablePred head] (h : ℕ) (p : List β) (hnd : p.Nodup)
    (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hh : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) → (∀ x ∈ c, head x) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ h) :
    p.length + 1 ≤ ((p.filter (fun x => decide (¬ head x))).length + 1) * 2 ^ h := by sorry
