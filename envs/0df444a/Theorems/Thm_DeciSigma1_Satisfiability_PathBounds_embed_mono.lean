-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_PathBounds_embed_mono
-- name    : DeciSigma1.Satisfiability.PathBounds.embed_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:39.048233+00:00
-- url     : https://prove2.me/theorems/4aab6b51-33f0-40c1-a4fc-117a9b24b205
-- title:
--   Path Bounds: embed mono
-- statement:
--   The Path Bounds construction uses the embed mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L94-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L94-L103

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

theorem DeciSigma1.Satisfiability.PathBounds.embed_mono (filler : Semantics.Tree n) (π : List (Fin n)) {t u : Semantics.Tree n}
    (h : t ≤ u) : embed filler π t ≤ embed filler π u := by sorry
