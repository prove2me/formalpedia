-- Prove2me | Theorems.Thm_DeciSigma1_Full_failures_iff_exists_leaf_witnesses
-- name    : DeciSigma1.Full.failures_iff_exists_leaf_witnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:19.646167+00:00
-- url     : https://prove2.me/theorems/ef273926-9350-43cf-99c7-d747118bbf23
-- title:
--   Full: failures iff exists leaf witnesses
-- statement:
--   All inequalities fail exactly when a mode and a path for each query give seeds in the solution
--   and exclusions outside it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L91-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L91-L100

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type}

theorem DeciSigma1.Full.failures_iff_exists_leaf_witnesses (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (q : Fin k → V × V) :
    (∀ i, ¬ Tree.Le c (ρ (q i).1) (ρ (q i).2)) ↔
      ∃ (m : Fin k → Bool) (W : Fin k → List (Fin n)), ∀ i,
        seed (q i) (m i) (W i) ∈ Closure.configSet c ρ ∧
        exclusion (q i) (m i) (W i) ∉ Closure.configSet c ρ := by sorry
