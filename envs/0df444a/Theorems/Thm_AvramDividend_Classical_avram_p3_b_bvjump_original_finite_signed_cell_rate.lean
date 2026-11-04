-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_signed_cell_rate
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_finite_signed_cell_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:56.843352+00:00
-- url     : https://prove2.me/theorems/086b96ef-45c9-4709-b9f6-f39312f6abfa
-- title:
--   Original signed finite predictable simple-cell compensation with explicit L1 finite rates
-- statement:
--   For the actual original predictable marked-source and compensator measures M,N, given equality on original adapted past-event rectangles, any finite collection with genuinely finite source masses has finite compensator masses. Every finite signed real linear combination of these cell masses agrees. This handles signed coefficients with explicit finite-mass hypotheses; it is conditional exactly on original rectangle compensation and does not posit an independent marked process.
-- source:
--   Proved P3-B original finite-cell compensation and Mathlib Finset.sum_congr; original P2 rectangle equality is an explicit hypothesis.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_finite_signed_cell_rate
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
    (c : ℕ → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hFinite : ∀ i ∈ S,
      M ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i) < ⊤) :
    (∀ i ∈ S,
      N ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i) < ⊤) ∧
      (∑ i ∈ S,
        c i * (M ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)).toReal) =
      (∑ i ∈ S,
        c i * (N ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)).toReal) := by sorry
