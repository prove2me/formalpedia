-- Prove2me | Theorems.Thm_Auto_sqrtOneMinusGaussian_lower
-- name    : Auto.sqrtOneMinusGaussian_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:57:30.213306+00:00
-- url     : https://prove2.me/theorems/7d9dcd60-229a-4b82-9da2-98f9428f1ae6
-- title:
--   Auto: sqrt One Minus Gaussian lower
-- statement:
--   **Proposition.**
--
--   The function
--
--   $$
--           f(x)=\sqrt{1-\mathfrak{g}(x)}
--   $$
--
--   is well-defined
--   using the nonnegative square root and is continuous on $\mathbb{R}$.
--   For $|x|\le \frac 12$, we have
--
--   $$
--           f(x)\ge \tfrac 12 |x|
--   $$
--
--   and for $|x|\ge \frac 12$ we have
--
--   $$
--           1-\mathfrak{g}(x)\le f(x)\le 1.
--   $$
--
--   See also `Auto.sqrtOneMinusGaussian`,
--   `Auto.sqrtOneMinusGaussian_wellDefined`,
--   `Auto.continuous_sqrtOneMinusGaussian`,
--   `Auto.sqrtOneMinusGaussian_bounds`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1686-L1736
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1686-L1736

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

theorem Auto.sqrtOneMinusGaussian_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    1 / 2 * |x| ≤ sqrtOneMinusGaussian x := by sorry
