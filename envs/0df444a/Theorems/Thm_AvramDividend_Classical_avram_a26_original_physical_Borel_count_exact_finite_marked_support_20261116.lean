-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
-- name    : AvramDividend.Classical.avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:35:30.255988+00:00
-- url     : https://prove2.me/theorems/efd5b548-13c8-416d-9490-c848c24b6a8a
-- title:
--   Original finite-activity physical negative Borel jump count equals the exact finite marked-time support cardinal
-- statement:
--   For the original spectrally negative Lévy process with finite negative activity, and any measurable negative Borel mark set B, the actual physical B-marked jump-time set in (0,T] is finite almost surely and its cardinal equals the original measurable representative K of the physical jump count. Derive directly from the proved same-source finite physical support theorem c6cc76c9 and exact marked-window count-cardinality theorem 8f1dd77e plus the given a.e. source equality hCount. No independent copy, source change, or Poisson-law assumption.
-- source:
--   Original physical marked times finite c6cc76c9 and original Borel window finite marked times cardinal 8f1dd77e, both Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    ∀ᵐ ω ∂P,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B) ∧
        K ω = S.card := by sorry
