-- Prove2me | Theorems.Thm_Auto_aux_hermiteParity_card_le
-- name    : Auto.aux_hermiteParity_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:02.264685+00:00
-- url     : https://prove2.me/theorems/ceaaa300-3a5d-481c-9253-438e9adc1dc4
-- title:
--   Auto: aux hermite Parity card le
-- statement:
--   This auxiliary cardinality bound counts the parity-compatible nonzero terms in the
--   Hermite polynomial expansion.  It is used to sum the termwise estimate in
--   `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L376-L411
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L376-L411

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

theorem Auto.aux_hermiteParity_card_le (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun d => Even (m + d))).card ≤ m / 2 + 1 := by sorry
