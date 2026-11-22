-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_Sat_add_const
-- name    : DeciSigma1.Arithmetic.DifferenceSystem.Sat.add_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:44.062579+00:00
-- url     : https://prove2.me/theorems/f9a215cf-57fe-437c-89e4-d52eaf429ea3
-- title:
--   Sat: add const
-- statement:
--   The Sat construction uses the add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L111-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean#L111-L114

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

theorem DeciSigma1.Arithmetic.DifferenceSystem.Sat.add_const {x : ι → ℤ} (h : D.Sat x) (c : ℤ) : D.Sat (fun i => x i + c) := by sorry
