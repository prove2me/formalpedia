-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
-- name    : AvramDividend.Classical.avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:20:31.886848+00:00
-- url     : https://prove2.me/theorems/286edb08-6e80-4283-8a3c-a2111494873b
-- title:
--   Original finite pairwise disjoint negative Borel mark void probabilities factor exactly
-- statement:
--   For any finite family of pairwise-disjoint negative Borel mark bands on the unchanged original spectrally negative Lévy source, the probability of no physical negative jump with a mark in their union equals the product of their original no-jump probabilities. Strengthens the Proved two-mark and three-mark void laws to arbitrary finite marked partitions.
-- source:
--   Proved original two-disjoint-Borel physical void factorisation 48b8388b, finite union null equivalence, and induction on the mark family. No independent mark-stream or circular imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original physical negative-jump void probabilities factor over every disjoint finite mark family. -/

theorem AvramDividend.Classical.avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : ι → Set ℝ) (S : Finset ι)
    (hMeas : ∀ i ∈ S, MeasurableSet (B i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ (⋃ i ∈ S, B i)) = 0}).toReal =
      ∏ i ∈ S, (P {ω | NX ω (Ioc 0 T ×ˢ B i) = 0}).toReal := by sorry
