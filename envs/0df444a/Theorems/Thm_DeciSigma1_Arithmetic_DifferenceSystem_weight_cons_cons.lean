-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:01.053151+00:00
-- url     : https://prove2.me/theorems/b13e1b66-7976-4565-b09e-c10a633d3fc6
-- title:
--   Difference System: weight cons cons
-- statement:
--   The Difference System construction uses the weight cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L87-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L87-L88

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons (i j : ι) (p : List ι) :
    D.weight (i :: j :: p) = (D.edgeWeight i j).getD 0 + D.weight (j :: p) := by sorry

attribute [defeq] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
