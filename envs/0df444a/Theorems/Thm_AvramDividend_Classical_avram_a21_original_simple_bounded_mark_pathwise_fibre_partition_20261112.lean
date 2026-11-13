-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
-- name    : AvramDividend.Classical.avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:58:56.800959+00:00
-- url     : https://prove2.me/theorems/6509baaf-1f99-477a-b35c-45a69f460b43
-- title:
--   Source physical marked integral equals finite simple-fibre count partition almost surely
-- statement:
--   Under finite original negative jump activity, each uniformly bounded original finite-valued real mark function has a physically integrable signed marked jump integral on a negative Borel mark set and that integral is exactly its finite disjoint fibres' original marked jump counts weighted by mark value, almost surely under the same P.
-- source:
--   Proved original physical finite jump count a.e. over all horizons ebd98fb4-754c-46ce-a419-23a731c44d69 and Proved measurable real simple mark integral partition 8360c4c0-c760-4abd-b89a-b281a4bbdf83; original physical Ω/P/filtration and marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) =
        ∑ y ∈ g.range, y *
          (NX ω (Ioc 0 T ×ˢ (S ∩ g ⁻¹' {y}))).toReal := by sorry
