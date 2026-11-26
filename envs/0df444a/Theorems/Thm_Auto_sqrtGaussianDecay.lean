-- Prove2me | Theorems.Thm_Auto_sqrtGaussianDecay
-- name    : Auto.sqrtGaussianDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:53.710774+00:00
-- url     : https://prove2.me/theorems/96ee320f-9d88-5e64-bf8b-780c91cb1ed8
-- title:
--   Auto: sqrt Gaussian Decay
-- statement:
--   **Proposition (square root of Gaussian decay).**
--
--   For $x\in\mathbb{R}$ let
--
--   $$
--   \rho(x) = \mathcal{F}^{-1}(\xi \mapsto 1- \sqrt{1-\mathfrak{g}(\xi)})(x).
--   $$
--
--   This is a well-defined function in $W_0(\mathbb{R})$ satisfying for all $x\in\mathbb{R}$,
--
--   $$
--       0\le \rho(x) \le C_{\text{square root of Gaussian decay}} \langle x\rangle^2,
--   $$
--
--   where $C_{\text{square root of Gaussian decay}}=17$.
--
--   See also `Auto.sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5650-L5659
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5650-L5659

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

theorem Auto.sqrtGaussianDecay :
    MemW0 aux_sqrtGaussianDecayKernel ∧
      ∀ x : ℝ, 0 ≤ aux_sqrtGaussianDecayKernel x ∧
        aux_sqrtGaussianDecayKernel x ≤
          C_squareRootGaussianDecay * bracketBump x ^ 2 := by sorry
