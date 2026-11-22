-- Prove2me | Theorems.Thm_DeciSigma1_Full_failure_iff_exists_leaf_witness
-- name    : DeciSigma1.Full.failure_iff_exists_leaf_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:38.352345+00:00
-- url     : https://prove2.me/theorems/fa9892a0-5bf5-42b8-ad4d-c7e390cb49ea
-- title:
--   Full: failure iff exists leaf witness
-- statement:
--   An inequality fails exactly when, for some mode and path, its seed belongs to the solution and
--   its exclusion does not.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L74-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L74-L87

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

theorem DeciSigma1.Full.failure_iff_exists_leaf_witness (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (q : V × V) :
    ¬ Tree.Le c (ρ q.1) (ρ q.2) ↔ ∃ m w,
      seed q m w ∈ Closure.configSet c ρ ∧ exclusion q m w ∉ Closure.configSet c ρ := by sorry
