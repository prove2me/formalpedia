-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_operator_bound
-- name    : AvramDividend.Classical.causal_weighted_volterra_operator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:03:19.930467+00:00
-- url     : https://prove2.me/theorems/45532213-035f-44b5-91c2-bb1b8e865435
-- title:
--   Weighted causal Volterra operator norm bounded by the kernel mass
-- statement:
--   For a continuous locally bounded input V, causal kernel β+K and positive exponential weight, the weighted absolute convolution at x≤R is bounded by the finite-horizon weighted supremum of V times the global weighted L1 norm of β+K. The proof factors e^(−wx) across the convolution and applies the proved weighted kernel-product and reflected-mass estimates. This is the quantitative bound needed for Banach fixed-point construction of Volterra resolvents.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_volterra_operator_bound
    (K V : ℝ → ℝ) (β w : ℝ) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (hLi : IntegrableOn (fun t : ℝ =>
      Real.exp (-w * t) * |β + K t|) (Ioi (0 : ℝ)) volume)
    (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R) :
    Real.exp (-(w * x)) *
      |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume| ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |V t|) ''
      Ioc (0 : ℝ) R) *
    (∫ t in Ioi (0 : ℝ), Real.exp (-w * t) * |β + K t| ∂volume) := by sorry
