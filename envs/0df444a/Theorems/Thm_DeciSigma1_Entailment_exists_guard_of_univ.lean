-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_exists_guard_of_univ
-- name    : DeciSigma1.Entailment.exists_guard_of_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:46.317805+00:00
-- url     : https://prove2.me/theorems/58e9c23f-4721-49a9-8bbd-f04741035b1f
-- title:
--   Entailment: exists guard of univ
-- statement:
--   In a class that contains the tree all of whose paths are labeled `f`, every assignment lies
--   below this tree, which is a guard.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L152-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L152-L154

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}

theorem DeciSigma1.Entailment.exists_guard_of_univ {C : PrefixSet n → Prop} (hC : C PrefixSet.univ)
    (ρ : V → PrefixSet n) : ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g := by sorry
