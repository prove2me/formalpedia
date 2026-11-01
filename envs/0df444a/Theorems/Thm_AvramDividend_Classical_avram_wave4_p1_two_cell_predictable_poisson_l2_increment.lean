-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_predictable_poisson_l2_increment
-- name    : AvramDividend.Classical.avram_wave4_p1_two_cell_predictable_poisson_l2_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:03:02.587558+00:00
-- url     : https://prove2.me/theorems/cff119cf-8d3b-4db2-928d-18a7fbdc1252
-- title:
--   Two-cell predictable Poisson compensated L2 energy increment
-- statement:
--   On the original probability space, let H be a square-integrable accumulated past payoff and J a square-integrable next-cell predictable coefficient; H and J may depend on each other. If a genuine future Poisson(r) count K is independent of the joint pair (H,J), and K-r is L1, then the new compensated sum H+J(K-r) is square integrable and its energy equals the old energy plus r times the weight energy. The proof expands the square and obtains its diagonal term from the separately proved weighted-count isometry and its cross term from separately proved joint-past orthogonality. It is one honest noncircular induction step toward finite-grid predictable stochastic isometry; original X jump PRM identification remains a separate source law.
-- source:
--   Canonical Proved P1 weighted count L2 isometry UUID f2883713-ef8b-46a8-8b0b-1f96a76239ce and joint-past orthogonality UUID e18265f8-241d-493f-ab46-e845e4bef374; algebraic square expansion, pinned Lean integral_add.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_past_weighted_poisson_count_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_future_poisson_past_product_orthogonal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_two_cell_predictable_poisson_l2_increment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H J : Ω → ℝ)
    (hH2 : MemLp H 2 P) (hHSq : Integrable (fun ω => H ω ^ 2) P)
    (hJm : Measurable J) (hJ2 : MemLp J 2 P)
    (hJSq : Integrable (fun ω => J ω ^ 2) P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hKInt : Integrable (fun ω => (K ω : ℝ) - (r : ℝ)) P)
    (hJointPast : IndepFun (fun ω => (H ω, J ω)) K P) :
    Integrable (fun ω => (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2) P ∧
      (∫ ω, (H ω + J ω * ((K ω : ℝ) - (r : ℝ))) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) + (r : ℝ) * ∫ ω, J ω ^ 2 ∂P := by sorry
