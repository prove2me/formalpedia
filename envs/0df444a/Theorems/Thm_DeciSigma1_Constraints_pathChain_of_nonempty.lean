-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_pathChain_of_nonempty
-- name    : DeciSigma1.Constraints.pathChain_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:54.498182+00:00
-- url     : https://prove2.me/theorems/19972380-b019-464b-8e31-e054e2009522
-- title:
--   Constraints: path Chain of nonempty
-- statement:
--   A path judgment that is reflexive, composes and factors along paths gives a chain along every
--   nonempty path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L552-L590
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L552-L590

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.pathChain_of_nonempty {α : Type*} (R : List (Fin n) → α → α → Prop)
    (hrefl : ∀ x, R [] x x)
    (hcomp : ∀ {π τ x y z}, R π x y → R τ y z → R (π ++ τ) x z)
    (hfactor : ∀ {π τ x z}, R (π ++ τ) x z → ∃ y, R π x y ∧ R τ y z)
    {π : List (Fin n)} {z x : α} (hπ : π ≠ []) (h : R π z x) :
    PathChain R π z x := by sorry
