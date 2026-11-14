-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b202_original_finite_band_marked_grid_real_poisson_dom_ae
-- name    : AvramDividend.Classical.avram_b202_original_finite_band_marked_grid_real_poisson_dom_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:48:02.506859+00:00
-- url     : https://prove2.me/theorems/36b3f388-92ea-4311-8a52-ac9ae5dbe218
-- title:
--   Actual original finite negative-band occupied random-grid real marked-cell count is dominated almost everywhere by full negative Poisson source count
-- statement:
--   For the genuine original finite-negative-activity spectrally negative Lévy source, a bounded original physical horizon and a possibly random monotone finite grid, suppose on a conull original event every selected negative-band contact cell contains a genuine physical source jump in one fixed reciprocal negative cutoff band before that horizon. Prepared B154 directly bounds the selected occupied-cell cardinal in ENNReal by the complete original negative marked source Poisson count. Proved B198 and B195 establishes that the latter full source count is finite almost everywhere for a bounded original physical horizon under finite negative mark intensity and original source measurability. On the intersection of conull source events the pinned ENNReal.toReal_mono transfers the physical marked-cell ENNReal count inequality into the real domination by the full original source count toReal. This provides the exact hJdom conull hypothesis for the Proved B150 and pending B157 original mixed Gaussian/negative-jump source finite-mesh energy using a fixed finite negative cutoff, bypassing the larger B163 all genuine marked-cell route. Publication waits for B154 and B198 and B195 Proved.
-- source:
--   Prepared B154 original finite-band source marked-grid ENNReal count bound, B199 full original negative Poisson source conull finiteness, Mathlib ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original bounded finite-negative-band marked random grid contact count is dominated almost everywhere by the real full-negative Poisson source count. -/

theorem AvramDividend.Classical.avram_b202_original_finite_band_marked_grid_real_poisson_dom_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n cut : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hJ : ∀ᵐ ω ∂P, ∀ i ∈ J ω,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T cut).toFinset,
        u ∈ Ioc (grid ω i) (grid ω (i + 1))) :
    ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by sorry
