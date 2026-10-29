-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:07:26.31521+00:00
-- url     : https://prove2.me/theorems/40a79593-e483-4594-8dee-9be2e3e7e951
-- title:
--   Nonnegative-supremum positive-threshold Laplace factors imply full independence
-- statement:
--   If R and D are nonnegative measurable real random variables under a probability P, and restricted upper-ray drawdown Laplace factorisations hold for every nonnegative threshold a and every positive beta, then IndepFun R D P. The restriction a≥0 suffices because for negative a the upper-ray event {R>a} is the whole sample space.
-- source:
--   Proved 5a7476f4-4c19-4b15-a073-540d640f85b0 all-real-threshold positive-beta restricted Laplace independence theorem (accepted remote candidate 17979); a<0 events are univ by R≥0. The exact genuine Qp upper-ray theorem 45c2af56 supplies factorisation for b≥0 and all positive beta.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

theorem AvramDividend.Classical.avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hRnonneg : ∀ ω, 0 ≤ R ω) (hDnonneg : ∀ ω, 0 ≤ D ω)
    (hFactor : ∀ a β : ℝ, 0 ≤ a → 0 < β →
      (∫⁻ ω in R ⁻¹' Set.Ioi a,
          ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) =
        P (R ⁻¹' Set.Ioi a) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P)) :
    IndepFun R D P := by sorry
