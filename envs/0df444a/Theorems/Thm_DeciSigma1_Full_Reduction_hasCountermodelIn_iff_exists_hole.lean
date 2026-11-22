-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_iff_exists_hole
-- name    : DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:24.884803+00:00
-- url     : https://prove2.me/theorems/a1c9c85e-fb3a-4c90-ac55-723741621936
-- title:
--   Reduction: has Countermodel In iff exists hole
-- statement:
--   The Reduction construction uses the has Countermodel In iff exists hole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L294-L302
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L294-L302

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_hole (hs : ∃ ρ, SatT c ρ Γ) :
    HasCountermodelIn (fun _ => True) c Γ q ↔
      ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by sorry
