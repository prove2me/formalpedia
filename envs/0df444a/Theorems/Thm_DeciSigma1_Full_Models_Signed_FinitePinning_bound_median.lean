-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_bound_median
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.bound_median
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:01.319832+00:00
-- url     : https://prove2.me/theorems/b18f88c5-d6db-4906-992a-d06231b79f7c
-- title:
--   Finite Pinning: bound median
-- statement:
--   If two assignments satisfy a ground bound, so does their median with any third assignment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L202-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L202-L216

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

theorem DeciSigma1.Full.Models.Signed.FinitePinning.bound_median (b : GroundBound n V) {A A' D : V → Semantics.Tree n}
    (ha : b.Holds A) (hb : b.Holds A') :
    b.Holds (fun v => treeMedian (A v) (A' v) (D v)) := by sorry
