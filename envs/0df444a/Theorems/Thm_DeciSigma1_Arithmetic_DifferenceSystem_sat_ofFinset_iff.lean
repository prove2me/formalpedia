-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_sat_ofFinset_iff
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.sat_ofFinset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:04.700796+00:00
-- url     : https://prove2.me/theorems/3374eaa7-f0e9-4f55-b1b6-d8569e95374a
-- title:
--   Difference System: sat of Finset iff
-- statement:
--   The Difference System construction uses the sat of Finset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L376-L390
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L376-L390

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.sat_ofFinset_iff [DecidableEq ι] (E : Finset (ι × ι × ℤ)) (x : ι → ℤ) :
    (ofFinset E).Sat x ↔ ∀ e ∈ E, x e.1 + e.2.2 ≤ x e.2.1 := by sorry
