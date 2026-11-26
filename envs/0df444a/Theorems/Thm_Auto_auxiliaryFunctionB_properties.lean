-- Prove2me | Theorems.Thm_Auto_auxiliaryFunctionB_properties
-- name    : Auto.auxiliaryFunctionB_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:02:50.71875+00:00
-- url     : https://prove2.me/theorems/e38086b1-739c-5832-a0be-0644069ae196
-- title:
--   Auto: auxiliary Function B properties
-- statement:
--   **Proposition.**
--
--   With $p$ as in Proposition `Auto.poissonKernel`, define $B:\mathbb{R}\to \mathbb{R}$ by
--
--   $$
--       B(\xi)=1-\sqrt{1-\mathfrak{g}(\xi)}-\widehat{p}(\sqrt{\pi}\xi)\, .
--   $$
--
--   Then $B$ is smooth on $\mathbb{R}\setminus \{0\}$ and continuous on $\mathbb{R}$. The function $B'$
--   has a continuous extension to $\mathbb{R}$ which is integrable and the
--   function $B''$, extended to be $0$ at $0$, is Borel measurable and integrable on $\mathbb{R}$.
--   Moreover,
--
--   $$
--       \|B\|_1\le 6,\qquad
--       \|B'\|_1\le 12,\qquad
--       \|B''\|_1\le 68.
--   $$
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4755-L4776
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4755-L4776

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

theorem Auto.auxiliaryFunctionB_properties :
    Continuous auxiliaryFunctionB ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB ({0}ᶜ : Set ℝ) ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x) ∧
      Continuous auxiliaryFunctionBDerivative ∧
      Integrable auxiliaryFunctionBDerivative ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionBDerivative (auxiliaryFunctionBSecondDerivative x) x) ∧
      Measurable auxiliaryFunctionBSecondDerivative ∧
      Integrable auxiliaryFunctionBSecondDerivative ∧
      eLpNorm auxiliaryFunctionB 1 volume ≤ ENNReal.ofReal 6 ∧
      eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 12 ∧
      eLpNorm auxiliaryFunctionBSecondDerivative 1 volume ≤ ENNReal.ofReal 56 := by sorry
