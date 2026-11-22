-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_PathBounds_embed_repeat_le
-- name    : DeciSigma1.Satisfiability.PathBounds.embed_repeat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:03.66309+00:00
-- url     : https://prove2.me/theorems/6379f53f-1dcb-4cf1-beb0-fb54a943b1ba
-- title:
--   Path Bounds: embed repeat le
-- statement:
--   Iterating a lower self-bound preserves the bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L112-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L112-L119

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

theorem DeciSigma1.Satisfiability.PathBounds.embed_repeat_le {t : Semantics.Tree n} {π : List (Fin n)}
    (h : embed Tree.bot π t ≤ t) (m : ℕ) :
    embed Tree.bot (List.replicate m π).flatten t ≤ t := by sorry
