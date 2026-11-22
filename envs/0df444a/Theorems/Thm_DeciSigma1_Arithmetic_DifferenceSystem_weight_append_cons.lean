-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_append_cons
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_append_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:43.079094+00:00
-- url     : https://prove2.me/theorems/adb30a49-cac8-4ba6-84f5-547527a04f6f
-- title:
--   Difference System: weight append cons
-- statement:
--   The Difference System construction uses the weight append cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L90-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L90-L99

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_append_cons (s t : List ι) (j : ι) :
    D.weight (s ++ j :: t) = D.weight (s ++ [j]) + D.weight (j :: t) := by sorry
