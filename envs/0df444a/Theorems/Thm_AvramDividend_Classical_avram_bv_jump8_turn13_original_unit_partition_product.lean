-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_unit_partition_product
-- name    : AvramDividend.Classical.avram_bv_jump8_turn13_original_unit_partition_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:38:48.292595+00:00
-- url     : https://prove2.me/theorems/8ecb0ca2-feb6-470c-87ff-b759f7456076
-- title:
--   Original finite strict marked unit product partitions into equal time cells
-- statement:
--   The literal original spectrally negative Levy path's finite strictly negative marked jumps on (0,1] partition disjointly into n+1 half-open cells; the unit exponential product is their finite cell product.
-- source:
--   Finite-set partition algebra on the actual original marked jumps. Show that each u in (0,1] lies in exactly one cell ((i:T),(i+1)*T]; use Finset.prod over pairwise disjoint filtered parts, with NNReal arithmetic (n+1)*T=1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn13_original_unit_partition_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ ω : Ω, (∏ u ∈ J ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      ∏ i : Fin (n + 1), C i ω := by sorry
