-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b172_original_canonical_actual_marked_random_grid_count_integrable
-- name    : AvramDividend.Classical.avram_b172_original_canonical_actual_marked_random_grid_count_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:12:58.332458+00:00
-- url     : https://prove2.me/theorems/893d8b21-6ffd-48ff-a47a-e0a85edff480
-- title:
--   Canonical genuinely marked original random monotone finite-grid cells have finite expected count under finite negative activity
-- statement:
--   For the actual original finite-negative-activity spectrally negative Levy source, take a bounded arbitrary potentially random monotone physical clock grid and a finite set of indices whose right endpoints are all within the fixed bounded original source horizon. Select exactly those grid cells containing an actual nonzero physical original source jump in their half-open intervals. The selected genuinely marked Finset has a finite ENNReal expected cardinal under the original probability law. Prepared B165 provides finite expected cardinal for any selected random marked monotone grid cells under conull actual source jump witnesses and bounded source endpoints. The canonical Finset.filter construction automatically satisfies those witness and endpoint conditions pathwise, so the theorem follows directly without artificial selected-contact integrability or a second-moment assumption. This supplies the genuine physical marked-grid jump-contact count expected L1 input for finite-mesh stopped Ito-Meyer energy estimates. Publish only once B165 Proved.
-- source:
--   Prepared original B165 genuinely marked random finite-grid expected source count and canonical original actual physical jump Finset filter.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical actual original physically jump-containing cells of any bounded random monotone stopped grid have a finite expected count under finite negative Levy activity. -/

theorem AvramDividend.Classical.avram_b172_original_canonical_actual_marked_random_grid_count_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (S : Finset ℕ)
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by sorry
