-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pin_normalize_iff
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pin_normalize_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:28.111223+00:00
-- url     : https://prove2.me/theorems/cd7c57c2-0bdf-42c2-a37f-ec11dcc39f81
-- title:
--   Finite Pinning: pin normalize iff
-- statement:
--   The Finite Pinning construction uses the pin normalize iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L170-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L170-L175

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pin_normalize_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (ρ : V → Semantics.Tree n) :
    (pin c b s).Holds (normalized c ρ) ↔ b.HoldsWithVariance c ρ := by sorry
