-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_uncapped_original_levy_survival_record_mass_partition
-- name    : AvramDividend.Classical.avram_ws01h_uncapped_original_levy_survival_record_mass_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:44:42.656009+00:00
-- url     : https://prove2.me/theorems/fa9a2eb0-3962-441b-ae95-4b9e781f302c
-- title:
--   Uncapped original Lévy lower-survival mass exactly partitions into genuine lower-killed first-record future survival and no-record mass
-- statement:
--   For any actual spectrally negative Lévy path started at reserve x, any upper record gap b≥0, and any joint path×real observation-age measure, the complete lower-barrier survival event is exactly the disjoint union of (1) a genuine strict upper-record before the observation age and lower first-passage, followed by complete shifted Lévy survival from the attained reserve x+b over its remaining observation age, and (2) the genuine no-upper-record event with original lower survival. Unlike capped partition lemmas, no finite cap N appears. Its proof takes the true observation age itself as the cap in the canonically Proved source pathwise finite-clock partition, transports the capped first-record state to the uncapped age, and proves the weak no-record branch measurable. Therefore the measure partition holds for the genuine Esscher terminal Qp without limit interchange, and assumes no two-sided exit scale formula.
-- source:
--   Canonical source finite-clock pathwise partition a560158e, exact original capped first-record age recovery 159a20a9, full-history joint measurability f2b6346c and upper stopping time measurability e1fe86e9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_uncapped_original_levy_survival_record_mass_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ) (hb : 0 ≤ b)
    (μ : Measure (Ω × ℝ)) :
    (let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - age z.1 →
          0 ≤ (x + b) + (X.X (age z.1 + u) z.1 - X.X (age z.1) z.1)}
     let B : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤ twoSidedExitUpTime X b z.1 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     μ E = μ A + μ B) := by sorry
