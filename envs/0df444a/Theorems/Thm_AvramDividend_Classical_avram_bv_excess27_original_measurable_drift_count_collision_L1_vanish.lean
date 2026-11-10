-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
-- name    : AvramDividend.Classical.avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:23:00.026201+00:00
-- url     : https://prove2.me/theorems/32f0b234-d58c-42fb-82e7-ee56f0cc4601
-- title:
--   Original finite-BV physical drift-occupied collision error vanishes in mean without raw jump-set measurability
-- statement:
--   Genuine cofinal, strictly monotone original physical grids have expected collision excess vanishing in L1 when the occupied-cell count is represented measurably by original X drift-deficient increments. Proved 7df2397f gives a.e fine-grid equality to the source full negative jump count; Proved 4426d791 identifies the raw occupied index set with the original X drift-deficient index set; Proved b4452443 gives measurability of the finite indicator sum; Proved 2811485c is the dominated-convergence engine and Proved 2fdbada6 supplies the exact finite source intensity. No arbitrary collapsed grids or global B L1. This is the corrected count collision component needed by 4f605d76 and f3f336fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hStrict : ∀ n, StrictMono (grid n))
    (hZero : ∀ n, grid n 0 = 0)
    (hEnd : ∀ n, grid n (cells n) = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      (∑ i ∈ Finset.range (cells n),
        if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
           X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
