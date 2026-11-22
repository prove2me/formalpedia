-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_PathBounds_repeat_isSome
-- name    : DeciSigma1.Satisfiability.PathBounds.repeat_isSome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:22.542578+00:00
-- url     : https://prove2.me/theorems/a3ceadce-b5bc-4102-a753-91a42840564a
-- title:
--   Path Bounds: repeat is Some
-- statement:
--   Matching lower and upper cycles put every power of the path into the domain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L132-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L132-L145

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
open DeciSigma1.Satisfiability.PathBounds

theorem DeciSigma1.Satisfiability.PathBounds.repeat_isSome {t u : Semantics.Tree n} {π : List (Fin n)}
    (hl : embed Tree.bot π t ≤ t) (htu : t ≤ u)
    (hu : u ≤ embed Tree.top π u) (m : ℕ) :
    (t.fn (List.replicate m π).flatten).isSome := by sorry
