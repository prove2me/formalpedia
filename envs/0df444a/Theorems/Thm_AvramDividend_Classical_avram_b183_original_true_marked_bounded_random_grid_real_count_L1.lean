-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b183_original_true_marked_bounded_random_grid_real_count_L1
-- name    : AvramDividend.Classical.avram_b183_original_true_marked_bounded_random_grid_real_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:21:25.546212+00:00
-- url     : https://prove2.me/theorems/7a637b88-9662-4e2d-bba9-81177501a3e5
-- title:
--   Exact original bounded random monotone physical source jump-containing marked-grid real cardinal is integrable under finite negative activity
-- statement:
--   For the actual original finite-negative-activity spectrally negative Lévy process, any finite monotone potentially random original physical clock grid with measurable source endpoint maps and right endpoints within a bounded time horizon has an integrable real number of genuinely jump-containing cells. The canonical marked-grid Finset is defined by existence of an actual nonzero original left-limit jump in the cell half-open physical interval. B181 proves the real count measurable from the original random negative Poisson cutoff count measurability, the source count-positive iff physical jump lemma and countable cutoff exhaustion. B172 proves its ENNReal count has finite expectation under the genuine original Poisson intensity. Together these give Integrable of the real cardinal via the Mathlib definition of finite integral and the identity that the nonnegative real norm of a Nat cardinal converts exactly to its ENNReal cardinal. This directly supplies the source-faithful hJmeas and marked contact-count L1 hypotheses in Proved B150 and pending B157 mixed Gaussian negative-jump stopped Ito mesh energy, without all-path negative activity or global second moment. Publish when B181 and B172 are Proved.
-- source:
--   Prepared B181 true physical original random-grid marked-cell real cardinal measurability, prepared B172 ENNReal finite expected physical marked count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b181_original_random_grid_genuine_marked_source_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b172_original_canonical_actual_marked_random_grid_count_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The real number of exact original physical negative-jump occupied cells in any bounded measurable random monotone stopped grid is integrable. -/

theorem AvramDividend.Classical.avram_b183_original_true_marked_bounded_random_grid_real_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (S : Finset ℕ)
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Integrable (fun ω => ((J ω).card : ℝ)) P := by sorry
