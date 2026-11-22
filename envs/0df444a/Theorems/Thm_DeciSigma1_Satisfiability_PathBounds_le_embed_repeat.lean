-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_PathBounds_le_embed_repeat
-- name    : DeciSigma1.Satisfiability.PathBounds.le_embed_repeat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:22.650401+00:00
-- url     : https://prove2.me/theorems/e8769241-a450-4f60-bbf3-608f2240c475
-- title:
--   Path Bounds: le embed repeat
-- statement:
--   Iterating an upper self-bound preserves the bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L122-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L122-L129

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

theorem DeciSigma1.Satisfiability.PathBounds.le_embed_repeat {t : Semantics.Tree n} {π : List (Fin n)}
    (h : t ≤ embed Tree.top π t) (m : ℕ) :
    t ≤ embed Tree.top (List.replicate m π).flatten t := by sorry
