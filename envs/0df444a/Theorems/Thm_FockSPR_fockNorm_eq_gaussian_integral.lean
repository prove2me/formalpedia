-- Prove2me | Theorems.Thm_FockSPR_fockNorm_eq_gaussian_integral
-- name    : FockSPR.fockNorm_eq_gaussian_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:42.493305+00:00
-- url     : https://prove2.me/theorems/9356310f-65a5-4a07-855d-18ef629eb7fd
-- title:
--   Fock SPR: fock Norm eq gaussian integral
-- statement:
--   The Fock SPR construction uses the fock Norm eq gaussian integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Definitions.lean#L664-L713
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Definitions.lean#L664-L713

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

theorem FockSPR.fockNorm_eq_gaussian_integral {D : ℕ} (a : Fin D → ℂ) :
    (1 / Real.pi) * ∫ z : ℂ,
      ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
    fockNormSq a := by sorry
