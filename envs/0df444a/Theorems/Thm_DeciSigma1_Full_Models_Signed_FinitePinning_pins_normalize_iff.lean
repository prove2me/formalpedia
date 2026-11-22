-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_normalize_iff
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pins_normalize_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:18:26.009153+00:00
-- url     : https://prove2.me/theorems/814a6b21-d0c6-4e7f-884b-e67eed97ec0e
-- title:
--   Finite Pinning: pins normalize iff
-- statement:
--   The Finite Pinning construction uses the pins normalize iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L177-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L177-L180

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
open DeciSigma1.Full.Models.Signed.FinitePinning
variable {V : Type*}

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pins_normalize_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (ρ : V → Semantics.Tree n) :
    (∀ p ∈ pins c B, p.Holds (normalized c ρ)) ↔ ∀ b ∈ B, b.HoldsWithVariance c ρ := by sorry
