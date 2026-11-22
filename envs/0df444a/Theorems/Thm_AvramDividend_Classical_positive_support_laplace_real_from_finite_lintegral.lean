-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_support_laplace_real_from_finite_lintegral
-- name    : AvramDividend.Classical.positive_support_laplace_real_from_finite_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:49:54.381933+00:00
-- url     : https://prove2.me/theorems/72268e6a-8411-4bf8-b74b-6136858ff064
-- title:
--   Positive-supported finite ENNReal Laplace transform yields real integrability and equality
-- statement:
--   If a real measure U is supported strictly on positive heights and its ENNReal full-space Laplace transform ∫⁻exp(−sy)dU equals a finite nonnegative real c for s>0, the same exponential kernel is real-integrable over (0,∞) and its real integral equals c. This is a source-faithful conversion between the generic killed Bernstein potential's ENNReal Laplace formula and the original Avram renewal measure's real Laplace requirement. Its hypotheses do not assume any scale function, Lévy process or renewal target.
-- source:
--   Proved integral_eq_toReal_lintegral_ofReal_nonneg 725d1c1a; pinned lintegral_ofReal_ne_top_iff_integrable, restrict_eq_self_of_ae_mem and ENNReal.toReal_ofReal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_integral_eq_toReal_lintegral_ofReal_nonneg
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_support_laplace_real_from_finite_lintegral
    (U : Measure ℝ) (hIic : U (Iic (0 : ℝ)) = 0)
    (s c : ℝ) (hs : 0 < s) (hc : 0 ≤ c)
    (hLap : (∫⁻ y : ℝ,
      ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        ENNReal.ofReal c) :
    IntegrableOn (fun y : ℝ => Real.exp (-(s * y))) (Ioi 0) U ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(s * y)) ∂U) = c := by sorry
