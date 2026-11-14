-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
-- name    : AvramDividend.Classical.avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:27:11.524073+00:00
-- url     : https://prove2.me/theorems/e47fbd2d-d644-4c71-9f1c-f76519ed7ef8
-- title:
--   Canonical genuine physical marked-grid card is measurable and dominated by original full negative Poisson count in real-valued conull source
-- statement:
--   On the exact original finite-activity spectrally negative Levy process and a bounded monotone measurable potentially random physical source grid, the genuinely marked finite-cell selector has measurable cardinality and its real count is almost surely dominated by the complete original negative Poisson source count toReal, assuming almost-everywhere measurability of this source count. Proved B181 yields the canonical physically marked-cell count measurability, Proved B163 gives its pathwise ENNReal source-count bound and Proved B195 finite full-negative source count on a conull set. The original stopping-time and terminal source ledger remain separate. This packages the two contact count hypotheses for original B150/B182 stopped mesh energy without falsely converting infinite negative counts or replacing the source.
-- source:
--   Proved B181 B163 B195, genuine original same-filtration Poisson source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b181_original_random_grid_genuine_marked_source_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T)
    (hCountMeas : AEMeasurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))) P) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) ∧
    (∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) := by sorry
