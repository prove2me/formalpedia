-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:58.112068+00:00
-- url     : https://prove2.me/theorems/1c744629-8927-4726-b0ec-11974119e219
-- title:
--   Difference System: weight singleton
-- statement:
--   The Difference System construction uses the weight singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L85-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L85-L85

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton (i : ι) : D.weight [i] = 0 := by sorry

attribute [defeq] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
