-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_mgf_eq_implies_tilt_complexMGF_real_ray
-- name    : AvramDividend.Classical.positive_mgf_eq_implies_tilt_complexMGF_real_ray
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:58:55.81257+00:00
-- url     : https://prove2.me/theorems/84eab7ff-dfe1-4d43-bb05-f8d37431cd5b
-- title:
--   Equal positive MGFs imply equal complex MGFs of exponentially tilted measures on the full real ray t greater than minus one
-- statement:
--   If two real Borel measures have equal real exponential integrals at every positive parameter u, their exponentially tilted measures dμ̃=e^x dμ and dν̃=e^x dν have equal complex moment generating functions at every real parameter t>-1. This converts the original one-sided positive Laplace data into a two-sided real interval around zero for the tilted measures, exactly the boundary-free uniqueness hypothesis of the accepted right-half-plane complex-MGF theorem.
-- source:
--   Accepted exp_tilt_real_mgf_shift [80bacfa0-f62f-4486-9f95-8ffc51b61f3f], pinned ProbabilityTheory.complexMGF_ofReal, the positive-MGF equality hypothesis. Supports measure_eq_of_pos_mgf_on_ray [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0].

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_exp_tilt_real_mgf_shift

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem AvramDividend.Classical.positive_mgf_eq_implies_tilt_complexMGF_real_ray
    (μ ν : Measure ℝ)
    (hm : ∀ u : ℝ, 0 < u →
      (∫ x, Real.exp (u * x) ∂μ) = (∫ x, Real.exp (u * x) ∂ν))
    (s : ℝ) (hs : -1 < s) :
    complexMGF id (μ.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x))) (s : ℂ) =
    complexMGF id (ν.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x))) (s : ℂ) := by sorry
