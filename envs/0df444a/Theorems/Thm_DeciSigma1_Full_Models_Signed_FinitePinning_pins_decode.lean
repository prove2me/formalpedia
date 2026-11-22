-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_decode
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pins_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:09.277888+00:00
-- url     : https://prove2.me/theorems/310b163d-33c4-4d99-b9f1-937c5d58afa3
-- title:
--   Finite Pinning: pins decode
-- statement:
--   The Finite Pinning construction uses the pins decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L227-L231
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L227-L231

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pins_decode {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → Semantics.Tree n} (hf : Constraints.Signed.dual A = A)
    (h : ∀ p ∈ pins c B, p.Holds A) : ∀ b ∈ B, b.HoldsWithVariance c (decoded c A) := by sorry
