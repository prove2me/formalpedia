-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_sat_nonneg_of_no_positiveCycle
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_of_no_positiveCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:57.63669+00:00
-- url     : https://prove2.me/theorems/7526ade6-c119-4aa9-aa16-c134718bb5ab
-- title:
--   Difference System: exists sat nonneg of no positive Cycle
-- statement:
--   Without a positive cycle, the maximal weights of simple walks ending at each vertex (the
--   empty walk counts `0`) form a nonnegative solution bounded by
--   `(|ι| - 1) · maxNonnegativeWeight`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L179-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L179-L258

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
open Classical

theorem DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_of_no_positiveCycle [Fintype ι]
    (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ ((Fintype.card ι - 1 : ℕ) : ℤ) *
        D.maxNonnegativeWeight := by sorry
