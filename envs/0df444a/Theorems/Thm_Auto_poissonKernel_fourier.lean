-- Prove2me | Theorems.Thm_Auto_poissonKernel_fourier
-- name    : Auto.poissonKernel_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:27.700121+00:00
-- url     : https://prove2.me/theorems/a7c46f99-7d55-587e-878e-022438f1d1ab
-- title:
--   Auto: poisson Kernel fourier
-- statement:
--   **Proposition.**
--
--   Let
--
--   $$
--       p(x)=2(1+(2\pi x)^2)^{-1}.
--   $$
--
--   Then
--
--   $$
--       \widehat{p}(\xi)=e^{- |\xi|}.
--   $$
--
--   See also `Auto.poissonKernel`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2123-L2150
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2123-L2150

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

theorem Auto.poissonKernel_fourier :
    FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ)) =
      fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ) := by sorry
