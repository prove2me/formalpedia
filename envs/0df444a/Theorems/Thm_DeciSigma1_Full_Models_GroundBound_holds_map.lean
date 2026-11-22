-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_GroundBound_holds_map
-- name    : DeciSigma1.Full.Models.GroundBound.holds_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:12.219351+00:00
-- url     : https://prove2.me/theorems/f1a0382a-080f-4ceb-8337-766ea1bb7055
-- title:
--   Ground Bound: holds map
-- statement:
--   The Ground Bound construction uses the holds map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L290-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L290-L292

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Models.GroundBound.holds_map {V W : Type*} (f : V → W)
    (b : GroundBound n V) (ρ : W → Semantics.Tree n) :
    (b.map f).Holds ρ ↔ b.Holds (ρ ∘ f) := by sorry
