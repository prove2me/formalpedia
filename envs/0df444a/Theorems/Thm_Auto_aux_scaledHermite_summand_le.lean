-- Prove2me | Theorems.Thm_Auto_aux_scaledHermite_summand_le
-- name    : Auto.aux_scaledHermite_summand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:16.159876+00:00
-- url     : https://prove2.me/theorems/366ef62e-6dc3-4d45-96cb-b91834607046
-- title:
--   Auto: aux scaled Hermite summand le
-- statement:
--   This auxiliary applies the Hermite coefficient estimate and the Gaussian monomial
--   estimate to one parity-compatible term of the scaled Hermite expansion.  It is used to
--   bound the finite sum in `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L604-L673
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L604-L673

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

theorem Auto.aux_scaledHermite_summand_le (m d : ℕ) (x : ℝ) (hd : d ≤ m) (he : Even (m + d)) :
    |(Real.sqrt (2 * Real.pi)) ^ m *
        (((Polynomial.hermite m).coeff d : ℝ) *
          (Real.sqrt (2 * Real.pi) * x) ^ d) *
        Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))| ≤
      (19 * ((m + 1 : ℕ) : ℝ)) ^ ((m : ℝ) / 2) *
        Real.exp (-(Real.pi / 2) * x ^ 2) := by sorry
