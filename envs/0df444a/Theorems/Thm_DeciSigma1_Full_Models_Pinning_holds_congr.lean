-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Pinning_holds_congr
-- name    : DeciSigma1.Full.Models.Pinning.holds_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:19.60311+00:00
-- url     : https://prove2.me/theorems/24a26775-c4bc-4f55-b7de-ff4510a90d86
-- title:
--   Pinning: holds congr
-- statement:
--   The Pinning construction uses the holds congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L110-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L110-L130

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Full.Models.Pinning

theorem DeciSigma1.Full.Models.Pinning.holds_congr {V : Type*} (c : Fin n → Bool) (l : LitT n V)
    {ρ τ : V → Semantics.Tree n} (h : ∀ v ∈ vars l, ρ v = τ v) :
    HoldsT c ρ l ↔ HoldsT c τ l := by sorry
