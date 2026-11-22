-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_PathBounds_embed_cons
-- name    : DeciSigma1.Constraints.PathBounds.embed_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:04.201523+00:00
-- url     : https://prove2.me/theorems/572afef4-2ba9-4055-a341-e2a95bae6e05
-- title:
--   Path Bounds: embed cons
-- statement:
--   The Path Bounds construction uses the embed cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L501-L503
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L501-L503

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
open DeciSigma1.Constraints.PathBounds

theorem DeciSigma1.Constraints.PathBounds.embed_cons (filler t : Semantics.Tree n) (i : Fin n) (π : List (Fin n)) :
    embed filler (i :: π) t =
      Semantics.Tree.node (fun j => if j = i then embed filler π t else filler) := by sorry
