-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_homogeneous_weighted_sup_inequality
-- name    : AvramDividend.Classical.causal_homogeneous_weighted_sup_inequality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:57:10.171993+00:00
-- url     : https://prove2.me/theorems/52d3debf-88dd-44fe-bf49-6212eacd1610
-- title:
--   Homogeneous Volterra solution satisfies a weighted-supremum contraction inequality
-- statement:
--   With a>0, w>0, and strict weighted kernel norm bound (|β|/w+∫e^(−wt)|K(t)|dt)<a, a continuous locally bounded homogeneous Volterra solution D satisfies e^(−wx)|D(x)|≤(∫e^(−wt)|β+K(t)|dt/a)·sup_{0<t≤R} e^(−wt)|D(t)| for 0<x≤R. Use the weighted integral estimate, positive-kernel supremum domination and finite-to-global kernel mass bound.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_exponential_weighted_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_homogeneous_weighted_integral_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_homogeneous_weighted_sup_inequality
    (K D : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hDc : ContinuousOn D (Ioi (0 : ℝ)))
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ t : ℝ, t ∈ Ioc (0 : ℝ) R → |D t| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * D x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume) = 0)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ),
        |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∀ R : ℝ, 0 < R → ∀ x ∈ Ioc (0 : ℝ) R,
      Real.exp (-(w * x)) * |D x| ≤
        ((∫ t in Ioi (0 : ℝ),
          Real.exp (-w * t) * |β + K t| ∂volume) / a) *
        sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
          Ioc (0 : ℝ) R) := by sorry
