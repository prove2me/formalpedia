-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
-- name    : AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:20:21.022873+00:00
-- url     : https://prove2.me/theorems/4430448c-266a-4cdd-adeb-7fbbc5c88543
-- title:
--   Square-root local L¹ estimate and global envelope imply probability uniform integrability
-- statement:
--   A measurable real sequence on a probability space is uniformly integrable if its global L1 seminorms have a common finite envelope B and every restricted L1 seminorm is bounded by B times the square root of the event probability. The proof constructs an explicit positive small-measure threshold at each precision, applies the restriction estimate uniformly in the index and supplies the global boundedness required by Mathlib's probability uniform-integrability predicate.

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 1 P ≤ (B : ENNReal))
    (hlocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (P.restrict s) ≤
        (B : ENNReal) * (P s) ^ (1 / 2 : ℝ)) :
    UniformIntegrable Y 1 P := by sorry
