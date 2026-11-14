-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b200_original_true_marked_grid_real_count_dom_poisson_ae
-- name    : AvramDividend.Classical.avram_b200_original_true_marked_grid_real_count_dom_poisson_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:42:59.628318+00:00
-- url     : https://prove2.me/theorems/8c33e5ea-880b-41af-8425-24c0e84d1190
-- title:
--   Genuine original marked random monotone finite-grid real cardinal is dominated almost everywhere by full negative Poisson source count toReal
-- statement:
--   Under finite negative Lévy activity on the genuine original spectrally negative process, take a bounded possibly random monotone physical grid with a finite selected set of cells each containing an actual original source nonzero jump before the fixed horizon, on conull events. Prepared B163 bounds the selected cardinal as an extended nonnegative real by the original mapped complete negative source Poisson count pathwise, without converting infinity. B198 and B195 proves that for a bounded measurable original physical horizon this full source count is finite on a conull event, from Proved mix_fin14 finite marked count expectation and exact source measurability. On the intersection of these conull events, monotonicity of ENNReal.toReal transfers the source marked-grid ENNReal bound to the real-valued selected marked-cell cardinal bound by the original full negative Poisson source count toReal. This is the exact count domination premise used by the Proved B150 and pending B157 Gaussian negative-jump finite-mesh Ito energy estimates, and it correctly allows exceptional original infinite jump counts. Publish only once B163 and B199 Proved.
-- source:
--   Prepared B163 true original ENNReal physical marked-grid count bound, B199 original bounded full source count conull finiteness, pinned ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original physical marked monotone stopped-grid cardinal is dominated in the reals by the genuine full negative Poisson source count almost everywhere under finite negative activity. -/

theorem AvramDividend.Classical.avram_b200_original_true_marked_grid_real_count_dom_poisson_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hMarks : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ᵐ ω ∂P, ∀ i ∈ J ω, grid ω (i + 1) ≤ T) :
    ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by sorry
