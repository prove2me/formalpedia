-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_UpperLabel_cons_leF
-- name    : DeciSigma1.Satisfiability.UpperLabel.cons_leF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:31.62239+00:00
-- url     : https://prove2.me/theorems/df1ec283-1e34-49a6-a4ce-aba7442bf9b2
-- title:
--   Upper Label: cons le F
-- statement:
--   The Upper Label construction uses the cons le F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L101-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L101-L111

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.UpperLabel.cons_leF {π : List (Fin n)} {g : Semantics.Sym} {x : V} {b : Fin n → V}
    (hl : LitT.leF x b ∈ Γ) (i : Fin n) (h : UpperLabel Γ π g (b i)) :
    UpperLabel Γ (i :: π) g x := by sorry
