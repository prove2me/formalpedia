-- Prove2me | Theorems.Thm_Auto_gaussianRescale_convolution
-- name    : Auto.gaussianRescale_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:56:57.442603+00:00
-- url     : https://prove2.me/theorems/1f3f6340-45a9-54a1-a260-34fe56ac2fcc
-- title:
--   Auto: gaussian Rescale convolution
-- statement:
--   **Proposition (Elementary Gaussian properties).**
--
--   (i) $\mathfrak{g}\in \mathcal{S}(\mathbb{R})\subset W_0(\mathbb{R})$
--
--   (ii) $\widehat{\mathfrak{g}}=\mathfrak{g}$.
--
--   (iii) We have for $\lambda,\mu>0$
--
--   $$
--   \mathfrak{g}_{(\lambda)}*\mathfrak{g}_{(\mu)}=\mathfrak{g}_{(\sqrt{\lambda^2+\mu^2})}\, .
--   $$
--
--   (iv) We have for $\lambda>0$
--
--   $$
--        \widehat{\mathfrak{g}_{(\lambda)}}(\xi)=\mathfrak{g}(\lambda \xi)
--   $$
--
--   See also `Auto.gaussian_memSchwartz`,
--   `Auto.gaussian_memW0`,
--   `Auto.gaussian_fourier_fixed`,
--   `Auto.gaussianRescale_fourier`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1433-L1482
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1433-L1482

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

theorem Auto.gaussianRescale_convolution (a μ : ℝ) (ha : 0 < a) (hμ : 0 < μ) (x : ℝ) :
    (∫ y : ℝ, gaussianRescale a (x - y) * gaussianRescale μ y) =
      gaussianRescale (Real.sqrt (a ^ 2 + μ ^ 2)) x := by sorry
