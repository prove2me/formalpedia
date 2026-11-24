-- Prove2me | Theorems.Thm_FockSPR_monomial_integral_bound
-- name    : FockSPR.monomial_integral_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:12.375857+00:00
-- url     : https://prove2.me/theorems/02f24086-bab7-44f5-beaa-65b3fa239a14
-- title:
--   Fock SPR: monomial integral bound
-- statement:
--   The Fock SPR construction uses the monomial integral bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L315-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L315-L330

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR

theorem FockSPR.monomial_integral_bound {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∫ r in (j : ℝ)..(j + 1 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) ≤
      Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
        Real.exp (-(distToInterval (rStar n) j) ^ 2) := by sorry
