-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_snoc_snoc
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_snoc_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:41.819584+00:00
-- url     : https://prove2.me/theorems/18cbdbf2-6b9a-48e2-aaf8-724de394b029
-- title:
--   Difference System: weight snoc snoc
-- statement:
--   The Difference System construction uses the weight snoc snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L101-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L101-L103

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_snoc_snoc (s : List ι) (i j : ι) :
    D.weight (s ++ [i, j]) = D.weight (s ++ [i]) + (D.edgeWeight i j).getD 0 := by sorry
