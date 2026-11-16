-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
-- name    : AvramDividend.Classical.avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:12:16.971959+00:00
-- url     : https://prove2.me/theorems/1c7bbdef-a98b-4d0d-bce5-5a985bac5865
-- title:
--   Almost-everywhere finite ENNReal physical count with exact first and second moments obeys occupancy sandwich
-- statement:
--   For any original probability space, an ENNReal-valued count N with a.e.-finite values and an a.e.-equal measurable natural count K, if E[N.toReal]=r and E[N.toReal(N.toReal−1)]=r² with integrability, then r−r²/2 ≤ 1−P(N=0) ≤r. The equality of void events uses ENNReal.toReal_eq_zero_iff, excluding infinity by hFin. Transfer moments via a.e. congruence then apply the generic integrated Nat occupancy lemma. This isolates the purely measure-theoretic step from the actual original Lévy count source hypotheses.
-- source:
--   Mathlib Integrable.congr, integral_congr_ae, ENNReal.toReal_eq_zero_iff, measure_congr, probability complement, and a25 integrated occupancy.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℝ≥0∞) (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal)
    (hFin : ∀ᵐ ω ∂P, N ω < ⊤)
    (r : ℝ)
    (hFirst : Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) = r)
    (hSecond : Integrable
        (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2) :
    r - r ^ 2 / 2 ≤ 1 - (P {ω | N ω = 0}).toReal ∧
      1 - (P {ω | N ω = 0}).toReal ≤ r := by sorry
