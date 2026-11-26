-- Prove2me | Theorems.Thm_Auto_aux_hermiteCoeff_bound
-- name    : Auto.aux_hermiteCoeff_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:56.26662+00:00
-- url     : https://prove2.me/theorems/0c3647ca-699c-424f-90a9-4f0382ed177f
-- title:
--   Auto: aux hermite Coeff bound
-- statement:
--   This auxiliary real-valued form of `aux_hermiteCoeff_nat_bound` bounds a Hermite
--   coefficient of the parity occurring in the Gaussian derivative formula.  It is used
--   termwise in `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L309-L340
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L309-L340

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section

theorem Auto.aux_hermiteCoeff_bound (m d : ℕ) (hd : d ≤ m) (he : Even (m + d)) :
    |((Polynomial.hermite m).coeff d : ℝ)| ≤
      (2 : ℝ) ^ (m - (m - d) / 2) * (m : ℝ) ^ ((m - d) / 2) := by sorry
