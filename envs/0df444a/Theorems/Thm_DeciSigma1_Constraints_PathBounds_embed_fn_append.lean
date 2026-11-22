-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_PathBounds_embed_fn_append
-- name    : DeciSigma1.Constraints.PathBounds.embed_fn_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:36.53528+00:00
-- url     : https://prove2.me/theorems/e7449caa-2aba-4f3d-ad55-5756b721a701
-- title:
--   Path Bounds: embed fn append
-- statement:
--   The Path Bounds construction uses the embed fn append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L505-L509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L505-L509

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

theorem DeciSigma1.Constraints.PathBounds.embed_fn_append (filler t : Semantics.Tree n) (π τ : List (Fin n)) :
    (embed filler π t).fn (π ++ τ) = t.fn τ := by sorry
