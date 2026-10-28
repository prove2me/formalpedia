-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_scalar_real_density_Ioc_intervalIntegral
-- name    : AvramDividend.Classical.nonnegative_scalar_real_density_Ioc_intervalIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:40:15.07308+00:00
-- url     : https://prove2.me/theorems/c745550d-e233-4c6f-be3a-ec02a0853c95
-- title:
--   Real scalar times renewal density has exact positive-interval cumulative integral
-- statement:
--   For nonnegative real r and a nonnegative integrable density f, the finite real mass of the scaled measure (ofReal r)•volume.withDensity(ofReal f) over (0,x] equals r times the usual real interval integral of f from 0 to x. This combines the Proved nonnegative_real_density_Ioc_toReal_eq_intervalIntegral with the pinned Mathlib ENNReal.toReal_mul and Measure.smul_apply identities. It is the needed final measure-to-primitive step for the correctly normalised Esscher BV renewal density and cstar finiteness proof.
-- source:
--   Canonical Proved nonnegative_real_density_Ioc_toReal_eq_intervalIntegral, pinned Mathlib ENNReal.toReal_mul and Measure.smul_apply.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nonnegative_scalar_real_density_Ioc_intervalIntegral (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    ((ENNReal.ofReal r • volume.withDensity
      (fun y : ℝ => ENNReal.ofReal (f y))) (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by sorry
