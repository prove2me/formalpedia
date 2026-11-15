-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b247_original_ruinclipped_stopping_clock_canonical_marked_cell_count_L1_dom
-- name    : AvramDividend.Classical.avram_b247_original_ruinclipped_stopping_clock_canonical_marked_cell_count_L1_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:27:49.388086+00:00
-- url     : https://prove2.me/theorems/46d4d257-5d95-4f76-a012-060a5d751b18
-- title:
--   Original B236 ruin-clipped stopped-clock canonical negative jump marked-cell count automatically integrable and Poisson dominated
-- statement:
--   The original finite-activity canonical physically marked negative-jump cell count on v_i=min(i n/(m+1),sigma(omega)) is measurable and integrable and almost surely dominated by the original finite negative marked Poisson count on (0,n], whenever sigma is an original right-continuous filtration stopping time bounded by n. This removes the additional Measurable sigma hypothesis of B243 automatically from the actual B236 hσstop assumptions, and is directly applicable to the mixed Gaussian/negative-jump predictable physical Itô cash source and marked-cell L1 domination without post-ruin sampling.
-- source:
--   Proved original stopping clock measurable-from-filtration lemma converts hσstop to Measurable sigma; Proved B243 then gives actual stopped-grid marked-cell real count integrability and Poisson domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
import Theorems.Thm_AvramDividend_Classical_avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b247_original_ruinclipped_stopping_clock_canonical_marked_cell_count_L1_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    Measurable (fun ω => ((marked ω).card : ℝ)) ∧
    Integrable (fun ω => ((marked ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((marked ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) := by sorry
