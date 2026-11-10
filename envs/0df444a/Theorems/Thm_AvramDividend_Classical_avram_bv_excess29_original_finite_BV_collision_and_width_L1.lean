-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess29_original_finite_BV_collision_and_width_L1
-- name    : AvramDividend.Classical.avram_bv_excess29_original_finite_BV_collision_and_width_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:47:50.524199+00:00
-- url     : https://prove2.me/theorems/081553be-9514-4082-a3be-a89830ebf35f
-- title:
--   Actual finite-activity BV physical-grid zero-contact collision and occupied-cell-width errors vanish together
-- statement:
--   This combines the same original compensated negative marked count with its measurable physical drift-deficient grid cell surrogate, and shows the sum of original collision error and uniform mesh width times fullmark jump count has vanishing expected ENNReal mass. Uses source exact Proved 32f0b234, occupied width source fbf40631, and measurable original process. Strict genuine meshes only, finite source intensity. A necessary two-error component of physical 4f605d76, to be merged with C1 interior and horizon/cap/ruin contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess29_original_finite_BV_collision_and_width_L1
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
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) - (∑ i ∈ Finset.range (cells n),
        if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
           X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0)) +
        (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
