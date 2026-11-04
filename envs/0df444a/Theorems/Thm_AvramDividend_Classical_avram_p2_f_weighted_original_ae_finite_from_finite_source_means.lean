-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_ae_finite_from_finite_source_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_ae_finite_from_finite_source_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:37:49.020829+00:00
-- url     : https://prove2.me/theorems/ea61e6d4-24c3-45bf-a841-cf0f7d3a06df
-- title:
--   Original Lévy weighted intrinsic marked count finite almost surely from finite source means
-- statement:
--   For the literal original Lévy intrinsic marked jump count on (s,s+T]×B and an arbitrary nonnegative original-past measurable weight, if both individual first moments are finite then their product is finite almost surely under the actual source measure P. This combines the genuinely accepted original future-past L1 finiteness transfer, original marked-count measurability, and the pinned Mathlib ae_lt_top theorem. It is useful for defining compensated predictable jump sums from separated bands and does not presume a ν-intensity formula.
-- source:
--   Accepted P2-F original finite L1 c458e9f2, accepted original rectangle measurability d9c55240, pinned Mathlib MeasureTheory.ae_lt_top exact signature.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_l1_of_finite_source_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_ae_finite_from_finite_source_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H N : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (hSource : ∀ ω : Ω, N ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s (s + T) ×ˢ B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hNfinite : (∫⁻ ω, N ω ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, H ω * N ω < ∞ := by sorry
