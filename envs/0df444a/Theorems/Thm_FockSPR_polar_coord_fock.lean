-- Prove2me | Theorems.Thm_FockSPR_polar_coord_fock
-- name    : FockSPR.polar_coord_fock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:50.157432+00:00
-- url     : https://prove2.me/theorems/6e64498f-ae9e-4000-ac8b-d06aa3f6505b
-- title:
--   Fock SPR: polar coord fock
-- statement:
--   The Fock SPR construction uses the polar coord fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Definitions.lean#L475-L554
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Definitions.lean#L475-L554

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex Real Finset
open scoped ENNReal NNReal
noncomputable section
open FockSPR

theorem FockSPR.polar_coord_fock {D : ℕ} (a : Fin D → ℂ) :
    rhoFockNormSq a = 2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) := by sorry
