-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_PathBounds_embed_append
-- name    : DeciSigma1.Satisfiability.PathBounds.embed_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:46.338057+00:00
-- url     : https://prove2.me/theorems/cdbc6117-4a39-40bb-bbe2-0adb9e9a21cc
-- title:
--   Path Bounds: embed append
-- statement:
--   The Path Bounds construction uses the embed append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L105-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L105-L109

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

theorem DeciSigma1.Satisfiability.PathBounds.embed_append (filler t : Semantics.Tree n) (π τ : List (Fin n)) :
    embed filler (π ++ τ) t = embed filler π (embed filler τ t) := by sorry
