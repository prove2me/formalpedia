-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_le_maxNonnegativeWeight
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.weight_le_maxNonnegativeWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:47.726268+00:00
-- url     : https://prove2.me/theorems/53494d72-50c0-449b-b889-567fdc2a28b3
-- title:
--   Difference System: weight le max Nonnegative Weight
-- statement:
--   The Difference System construction uses the weight le max Nonnegative Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L130-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L130-L142

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.weight_le_maxNonnegativeWeight [Fintype ι] :
    ∀ p : List ι, D.IsWalk p → D.weight p ≤ (p.length - 1 : ℕ) * (D.maxNonnegativeWeight : ℤ)
  := by sorry
