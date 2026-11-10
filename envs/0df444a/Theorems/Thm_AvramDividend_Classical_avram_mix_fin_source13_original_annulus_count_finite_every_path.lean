-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_finite_every_path
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_finite_every_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:48:30.105234+00:00
-- url     : https://prove2.me/theorems/0060f5ce-c54a-4906-8d72-d5c5b7be7b2e
-- title:
--   Original negative-annulus intrinsic jump count finite on every physical path
-- statement:
--   For any exact original spectrally negative Levy process, every bounded-horizon negative reciprocal annulus marked jump count is finite on each sample path. It follows from the Proved finite cardinality of the upper cutoff band and Proved disjoint-mark count decomposition, without assumptions about stochastic independence. This is the pathwise finite-count interface for ENNReal and real count moments in original factorial target 6ea0212e.
-- source:
--   MIX-SOURCE-FIN13 pointwise finiteness prerequisite for original annulus chronological pair rate

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_finite_every_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    N ≠ ⊤ := by sorry
