-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_signDual
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pins_signDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:58.544118+00:00
-- url     : https://prove2.me/theorems/4b9ded6c-1d5e-4ea6-9fb7-a05c47e2b52e
-- title:
--   Finite Pinning: pins sign Dual
-- statement:
--   The Finite Pinning construction uses the pins sign Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L194-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L194-L199

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pins_signDual {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → Semantics.Tree n} (h : ∀ p ∈ pins c B, p.Holds A) :
    ∀ p ∈ pins c B, p.Holds (Constraints.Signed.dual A) := by sorry
