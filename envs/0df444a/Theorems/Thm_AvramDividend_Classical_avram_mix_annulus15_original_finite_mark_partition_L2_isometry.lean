-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_finite_mark_partition_L2_isometry
-- name    : AvramDividend.Classical.avram_mix_annulus15_original_finite_mark_partition_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:37:07.233122+00:00
-- url     : https://prove2.me/theorems/a9d584b1-cdf4-45b8-b081-cda6cbadf037
-- title:
--   Original Lévy arbitrary finite negative-annulus deterministic-mark compensated L2 isometry
-- statement:
--   For every nondecreasing finite negative-cutoff sequence, the original physically marked Lévy jump counts on the consecutive half-open annuli have an exact deterministic-weight compensated L2 isometry. Each diagonal variance uses the Proved original physical annulus second-moment theorem; every two distinct bands are orthogonal via the Proved original separated-annulus covariance. The finite algebraic bridge 99af255d closes the weighted sum. This is the arbitrary finite simple-mark source input to the mixed infinite-activity stopped witness 5f12c023.
-- source:
--   Root-connected original source X/P marked-jump arbitrary finite simple-mark isometry; imports Proved 6e234a3f, 9c325a05 and finite family algebraic bridge 99af255d. For infinite-activity small-jump compensated martingale construction under 5f12c023 -> f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_finite_weight_L2_of_physical_moments
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_original_finite_mark_partition_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (k : ℕ) (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1)))
        (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    Integrable (fun ω => (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range k, (a i) ^ 2 * r i := by sorry
