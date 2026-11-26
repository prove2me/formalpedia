-- Prove2me | solution 1 for contourIntegral_contourIntegral_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:04.954819+00:00
-- url     : https://prove2.me/submissions/7986b1b5-941e-48e9-a71e-e4d2a92e4436

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → ℂ → F) (gamma delta : ℝ → ℂ)
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv gamma x.1 •
        (deriv delta x.2 • f (gamma x.1) (delta x.2)))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi))) :
    contourIntegral (fun z => contourIntegral (f z) delta) gamma =
      contourIntegral (fun w => contourIntegral (fun z => f z w) gamma)
        delta := by
  unfold contourIntegral
  calc
    (∫ s in (0 : ℝ)..(2 * Real.pi), deriv gamma s •
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          deriv delta t • f (gamma s) (delta t)) =
        ∫ s in (0 : ℝ)..(2 * Real.pi),
          ∫ t in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s •
              (deriv delta t • f (gamma s) (delta t)) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      change deriv gamma s •
          (∫ t in (0 : ℝ)..(2 * Real.pi),
            deriv delta t • f (gamma s) (delta t)) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), deriv gamma s •
          (deriv delta t • f (gamma s) (delta t))
      rw [intervalIntegral.integral_smul]
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s •
              (deriv delta t • f (gamma s) (delta t)) := by
      exact MeasureTheory.intervalIntegral_intervalIntegral_swap hint
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv delta t •
              (deriv gamma s • f (gamma s) (delta t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      apply intervalIntegral.integral_congr
      intro s _hs
      exact smul_comm _ _ _
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi), deriv delta t •
          ∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s • f (gamma s) (delta t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (∫ s in (0 : ℝ)..(2 * Real.pi), deriv delta t •
          (deriv gamma s • f (gamma s) (delta t))) =
        deriv delta t •
          (∫ s in (0 : ℝ)..(2 * Real.pi),
            deriv gamma s • f (gamma s) (delta t))
      rw [intervalIntegral.integral_smul]
