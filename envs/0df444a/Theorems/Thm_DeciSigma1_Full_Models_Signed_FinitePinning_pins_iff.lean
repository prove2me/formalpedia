-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_iff
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pins_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:18:24.603772+00:00
-- url     : https://prove2.me/theorems/0151d616-e75e-4146-8ebc-8dc8f352f9cc
-- title:
--   Finite Pinning: pins iff
-- statement:
--   The Finite Pinning construction uses the pins iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L155-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L155-L168

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pins_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (A : V × Bool → Semantics.Tree n) :
    (∀ p ∈ pins c B, p.Holds A) ↔ ∀ b ∈ B, ∀ s, (pin c b s).Holds A := by sorry
