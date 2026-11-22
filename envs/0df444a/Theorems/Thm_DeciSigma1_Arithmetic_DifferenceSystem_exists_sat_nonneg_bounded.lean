-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_sat_nonneg_bounded
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:58.379827+00:00
-- url     : https://prove2.me/theorems/50ce14ce-2f7e-49ae-9404-ff31e490a2d4
-- title:
--   Difference System: exists sat nonneg bounded
-- statement:
--   A system without positive cycles has a nonnegative solution bounded by
--   `|ι| · maxNonnegativeWeight`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L262-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L262-L266

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_bounded [Fintype ι] (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ (Fintype.card ι : ℤ) * D.maxNonnegativeWeight := by sorry
