-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor
-- name    : AvramDividend.Classical.esscher_root_real_positive_geometric_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:21:27.825724+00:00
-- url     : https://prove2.me/theorems/4945bae8-16e4-49f1-a0a3-38399f90abc9
-- title:
--   Esscher-root integral gap yields strict Laplace crossing and the ENNReal geometric reciprocal
-- statement:
--   For a nonnegative Lévy jump magnitude measure, a discounted jump compensator integrable at an Esscher root and a strict positive-Laplace kernel bound below the bounded-variation drift, convert the kernel's ENNReal transform into its real compensator integral. Deduce q<ψ(φ+s) from the exact root-shifted Lévy exponent denominator and rewrite the positive geometric renewal reciprocal as 1/(ψ(φ+s)-q). All integrability requirements are explicit.
-- source:
--   Avram Palmowski Pistorius 2007 section 2 bounded-variation Lévy exponent; Kuznetsov Kyprianou Rivero Theory of Scale Functions 2012; pinned Prove2Me accepted positive_geometric_transform_real_reciprocal.

import Theorems.Thm_AvramDividend_Classical_positive_geometric_transform_real_reciprocal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_root_real_positive_geometric_factor
    (μ : Measure ℝ≥0) (φ δ s q ψval : ℝ)
    (hδ : 0 < δ) (hs : 0 < s)
    (hint : Integrable
      (fun z : ℝ≥0 => Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ))))) μ)
    (hψ : ψval - q = δ * s -
       (∫ z : ℝ≥0, Real.exp (-(φ * (z : ℝ))) *
          (1 - Real.exp (-(s * (z : ℝ)))) ∂μ))
    (r : ℝ≥0∞)
    (hr : r = ∫⁻ z : ℝ≥0,
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
          ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s) ∂μ)
    (hgap : r < ENNReal.ofReal δ) :
    q < ψval ∧
      ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal δ)⁻¹ *
          (1 - (ENNReal.ofReal δ)⁻¹ * r)⁻¹) =
        ENNReal.ofReal ((ψval - q)⁻¹) := by sorry
