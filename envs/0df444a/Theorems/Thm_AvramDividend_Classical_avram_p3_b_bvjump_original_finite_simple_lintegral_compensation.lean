-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_simple_lintegral_compensation
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_finite_simple_lintegral_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:30:44.750606+00:00
-- url     : https://prove2.me/theorems/3dc2ee0e-0d55-4f01-abb2-1024c0e8a4af
-- title:
--   Original predictable marked finite-simple integrands have equal genuine lower integrals under source cell compensation
-- statement:
--   Given equality of masses on all original filtration predictable finite marked cylinders, the actual ENNReal lower integrals of any finite nonnegative adapted simple-cell function under both original marked measures agree. This uses the original 𝓕.rightCont.predictable measurable structure, the already Proved P3-B measurable-set lemma, Mathlib lintegral_finsetSum and indicator const, without finite intensity or hidden 0·∞ assumptions. Conditional on P2 finite original-source cell compensation, not an unconditional source martingale or alternative Poisson model.
-- source:
--   Mathlib.MeasureTheory.Integral.Lebesgue.Add lintegral_finsetSum and Lebesgue.Basic lintegral_indicator_const; accepted P3-B predictable finite-cell theorem; Avram Proposition 4(i).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_finite_simple_lintegral_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (A : ℕ → Set Ω) (B : ℕ → Set ℝ)
    (c : ℕ → ℝ≥0∞)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (∫⁻ p, ∑ i ∈ S,
      (((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i).indicator
        (fun _ => c i)) p ∂M) =
    (∫⁻ p, ∑ i ∈ S,
      (((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i).indicator
        (fun _ => c i)) p ∂N) := by sorry
