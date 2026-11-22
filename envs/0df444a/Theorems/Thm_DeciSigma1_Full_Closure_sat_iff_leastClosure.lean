-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_sat_iff_leastClosure
-- name    : DeciSigma1.Full.Closure.sat_iff_leastClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:10.357397+00:00
-- url     : https://prove2.me/theorems/0a21aa69-c41c-4f11-a359-b03a8e59c5c7
-- title:
--   Closure: sat iff least Closure
-- statement:
--   A flat constraint is satisfiable exactly when its least closure avoids the negative facts and
--   is consistent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L488-L500
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L488-L500

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.sat_iff_leastClosure :
    (∃ ρ, SatT c ρ Γ) ↔ Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ) := by sorry
