-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys28_full_uniform_negative_collision_L1
-- name    : AvramDividend.Classical.avram_bv_phys28_full_uniform_negative_collision_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:44:50.096886+00:00
-- url     : https://prove2.me/theorems/5962720e-daa3-4afe-a451-5d8137750fe3
-- title:
--   Original finite-activity BV uniform physical negative-collision drift-count error vanishes in L1
-- statement:
--   For the exact original full-horizon uniform physical grid with n+2 cells, the original BV negative-jump count minus the count of drift-deficient cells has expected positive collision mass tending to zero. This is the source-exact fixed-horizon collision certificate needed to control zero-contact errors in finite activity.
-- source:
--   Instantiate Proved original source collision theorem 32f0b234 using genuine uniform positive cell widths. The parent's original prefix u n (n+1) is T minus the final width; extending to index n+2 reaches T without inventing a different path/process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys28_full_uniform_negative_collision_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      (∑ i ∈ Finset.range (n + 2),
        if X.X (u n (i + 1)) ω - X.X (u n i) ω <
           X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
