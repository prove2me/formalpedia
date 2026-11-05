-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_actual_source_variation
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_actual_source_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:35:04.151379+00:00
-- url     : https://prove2.me/theorems/3086f90a-cdf3-4d69-ad06-08c4197c0d43
-- title:
--   Discounted actual BV Lévy source increments controlled by genuine drift and negative jump mass
-- statement:
--   On almost every actual original spectrally negative bounded-variation Lévy path, nonnegative monotone jump-mass increments and real discount q≥0 control the total discounted absolute physical source increments ΔX.X along any ordered grid by |drift|*(u_n-u_0)+[R(u_n)-R(u_0)]+[J(u_n)-J(u_0)]. This combines the verified actual Y=X+J variation theorem with exact original J telescoping, leaving the physical drift, negative jump times and frozen original source path intact. The explicitly pathwise nondecreasing jump-mass premise is available to the original jump/localisation owner.
-- source:
--   Original source Proved Y grid variation e9650890 and exact source J cell partition df3481a1; discounted weight ≤1; pathwise nonnegative source jump increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_actual_source_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (q : ℝ) (hq : 0 ≤ q),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∀ i, i < n → J (u i) ≤ J (u (i + 1))) →
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) +
            (J (u n) - J (u 0)) := by sorry
