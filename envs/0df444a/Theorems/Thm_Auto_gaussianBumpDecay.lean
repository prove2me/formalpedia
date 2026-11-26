-- Prove2me | Theorems.Thm_Auto_gaussianBumpDecay
-- name    : Auto.gaussianBumpDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:30.524677+00:00
-- url     : https://prove2.me/theorems/0658932e-f07f-4f42-b59d-b46fd1e47ad8
-- title:
--   Auto: gaussian Bump Decay
-- statement:
--   **Proposition.**
--
--   For every $x\in\mathbb{R}$, $m,N\in\mathbb{N}$,
--
--   $$
--   |\mathfrak{g}^{(m)}(x)|\le C_{\text{Gaussian bump decay},m,N} \langle x\rangle^N,
--   $$
--
--   where
--
--   $$
--   C_{\text{Gaussian bump decay},m,N}
--   =\bigl(64(m+1)\bigr)^{m/2}\bigl(4(N+1)\bigr)^{N/2}.
--   $$
--
--   See also `Auto.gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L804-L823
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L804-L823

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

theorem Auto.gaussianBumpDecay (x : ℝ) (m N : ℕ) :
    |iteratedDeriv m gaussian x| ≤ C_gaussianBumpDecay m N * bracketBump x ^ N := by sorry
