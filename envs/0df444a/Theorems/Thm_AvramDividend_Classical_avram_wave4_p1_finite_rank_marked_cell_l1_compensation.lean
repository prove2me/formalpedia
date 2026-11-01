-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_cell_l1_compensation
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_cell_l1_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:17:39.720039+00:00
-- url     : https://prove2.me/theorems/bbd1e1c5-f3ca-4cd7-9a7d-7e2c5cea2e2c
-- title:
--   Finite-rank predictable L¹ Campbell identity for one original marked-Poisson cell
-- statement:
--   For an actual original-space Poisson(r) marked cell, every finite sum of nonanticipative past weight times mark profiles, with each measurable integrable past weight independent of the joint full future count-and-marks and each mark profile integrable, is genuinely integrable after centering and has exactly zero expectation. No martingale or Campbell formula is assumed; derive from proved one-cell marked compensation and product L1 integrability term by term. It handles multiple distinct past weights and mark profiles sharing the same future cell.
-- source:
--   WS1B canonical Proved one-cell closed marked Campbell UUID 33961fb8 and weighted random marked product-integrability UUID a467fb2d, pinned Finset integral and linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_cell_l1_compensation
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ι)
    (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ a ∈ s, Measurable (H a))
    (hHi : ∀ a ∈ s, Integrable (H a) μ)
    (hPast : ∀ a ∈ s,
      IndepFun (H a) (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hfm : ∀ a ∈ s, Measurable (f a))
    (hfI : ∀ a ∈ s, Integrable (f a) ν) :
    Integrable (fun ω => ∑ a ∈ s,
      H a ω * ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        (r : ℝ) * ∫ z, f a z ∂ν)) μ ∧
    (∫ ω, ∑ a ∈ s,
      H a ω * ((∑ n ∈ Finset.range (K ω), f a (Y n ω)) -
        (r : ℝ) * ∫ z, f a z ∂ν) ∂μ) = 0 := by sorry
