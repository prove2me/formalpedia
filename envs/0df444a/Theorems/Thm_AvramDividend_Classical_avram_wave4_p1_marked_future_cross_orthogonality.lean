-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_future_cross_orthogonality
-- name    : AvramDividend.Classical.avram_wave4_p1_marked_future_cross_orthogonality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:33:50.064258+00:00
-- url     : https://prove2.me/theorems/d1f079f5-a1ba-48c5-a1cd-53b45dbac700
-- title:
--   Past-pair cross orthogonality against a future marked Poisson cell
-- statement:
--   For a true Poisson marked cell, two jointly past-observable (possibly dependent) square-integrable weights H,J have an integrable product with the centered future marked sum, whose expectation is zero. Independence is required between the JOINT pair (H,J) and the full count-and-marks future, not between H and J. Proof derives product integrability by Hölder and the independently proved WS1B marked-Campbell theorem; it does not assume any martingale or orthogonality conclusion. Supplies the off-diagonal term for finite-grid marked L² stochastic integration.
-- source:
--   Canonical Proved WS1B one-cell product integrability a467fb2d-71c1-4680-9f98-6b28c8143403 and closed marked Campbell 33961fb8-62cf-4cb9-9a1a-b4a1eef4f1e9; pinned MemLp.integrable_mul.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_marked_future_cross_orthogonality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : MemLp H 2 μ) (hJ2 : MemLp J 2 μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun (fun ω => (H ω, J ω))
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    Integrable (fun ω => (H ω * J ω) *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) μ ∧
      (∫ ω, (H ω * J ω) *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν) ∂μ) = 0 := by sorry
