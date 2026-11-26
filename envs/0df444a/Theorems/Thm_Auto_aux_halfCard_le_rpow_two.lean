-- Prove2me | Theorems.Thm_Auto_aux_halfCard_le_rpow_two
-- name    : Auto.aux_halfCard_le_rpow_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:54.010541+00:00
-- url     : https://prove2.me/theorems/fd71c9e7-c1f1-542d-98b3-4779e7c5b2de
-- title:
--   Auto: aux half Card le rpow two
-- statement:
--   This auxiliary elementary estimate turns the cardinality in
--   `aux_hermiteParity_card_le` into the square-root power of two used in
--   `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L418-L439
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L418-L439

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

theorem Auto.aux_halfCard_le_rpow_two (m : ℕ) :
    ((m / 2 + 1 : ℕ) : ℝ) ≤ Real.rpow 2 ((m : ℝ) / 2) := by sorry
