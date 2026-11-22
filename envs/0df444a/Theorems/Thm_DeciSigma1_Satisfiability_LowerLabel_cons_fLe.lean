-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_LowerLabel_cons_fLe
-- name    : DeciSigma1.Satisfiability.LowerLabel.cons_fLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:27.839054+00:00
-- url     : https://prove2.me/theorems/9e1926a7-2857-44bd-9d9e-f173d92994fc
-- title:
--   Lower Label: cons f Le
-- statement:
--   The Lower Label construction uses the cons f Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L48-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L48-L58

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.LowerLabel.cons_fLe {π : List (Fin n)} {g : Semantics.Sym} {a : Fin n → V} {x : V}
    (hl : LitT.fLe a x ∈ Γ) (i : Fin n) (h : LowerLabel Γ π g (a i)) :
    LowerLabel Γ (i :: π) g x := by sorry
