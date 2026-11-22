-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_fn
-- name    : DeciSigma1.Satisfiability.leastShape_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:03.202189+00:00
-- url     : https://prove2.me/theorems/58f1b871-04f5-4f38-9b30-dbe29598c0ef
-- title:
--   Satisfiability: least Shape fn
-- statement:
--   The Satisfiability construction uses the least Shape fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L189-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L189-L193

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
open Classical

theorem DeciSigma1.Satisfiability.leastShape_fn (Γ : List (LitT n V)) (x : V) (π : List (Fin n)) :
    (leastShape Γ x).fn π =
      if Semantics.IsLivePrefix (shapeLabel Γ x) π then some (shapeLabel Γ x π) else none := by sorry
