-- Prove2me | solution 1 for crouzeixBoundaryDoubleLayerDensity_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:15.032125+00:00
-- url     : https://prove2.me/submissions/2cdad777-5fe8-4fa3-b134-d01e9e812c1f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
section
open Complex Filter MeasureTheory Set
open scoped Interval Real
private theorem periodic_deriv_boundaryParam (Omega : SmoothJordanDomain) :
    Function.Periodic (deriv Omega.boundaryParam) (2 * Real.pi) := by
  intro t
  have hfun : (fun x : ℝ => Omega.boundaryParam (x + 2 * Real.pi)) =
      Omega.boundaryParam := by
    funext x
    exact Omega.boundaryParam_periodic x
  have h := congrArg (fun f : ℝ → ℂ => deriv f t) hfun
  rwa [deriv_comp_add_const] at h
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    Function.Periodic
      (crouzeixBoundaryDoubleLayerDensity Omega xi) (2 * Real.pi) := by
  intro t
  unfold crouzeixBoundaryDoubleLayerDensity
  rw [periodic_deriv_boundaryParam Omega t,
    Omega.boundaryParam_periodic t]
