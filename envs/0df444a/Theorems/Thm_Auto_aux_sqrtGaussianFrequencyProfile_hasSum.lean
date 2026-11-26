-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianFrequencyProfile_hasSum
-- name    : Auto.aux_sqrtGaussianFrequencyProfile_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:03.280962+00:00
-- url     : https://prove2.me/theorems/5b442107-98e6-45ed-9d20-fa41628cae61
-- title:
--   Auto: aux sqrt Gaussian Frequency Profile has Sum
-- statement:
--   This auxiliary specialization of the binomial expansion writes the square-root Gaussian
--   frequency profile as a positive Gaussian mixture away from the origin.  It is used by the
--   positive-mixture proof of `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4505-L4516
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4505-L4516

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

theorem Auto.aux_sqrtGaussianFrequencyProfile_hasSum {x : ℝ} (hx : x ≠ 0) :
    @HasSum ℝ ℕ Real.instAddCommGroup.toAddCommMonoid _
      (fun n : ℕ => aux_sqrtGaussianCoefficient n *
        gaussian (Real.sqrt (n + 1) * x))
      (1 - sqrtOneMinusGaussian x) (SummationFilter.unconditional ℕ) := by sorry
