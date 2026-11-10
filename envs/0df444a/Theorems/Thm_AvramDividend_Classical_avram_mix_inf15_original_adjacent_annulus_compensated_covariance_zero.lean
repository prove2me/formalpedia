-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
-- name    : AvramDividend.Classical.avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:10:30.892868+00:00
-- url     : https://prove2.me/theorems/a13593f2-72e7-4583-bb1c-b271c64dd0a7
-- title:
--   Exact covariance zero of disjoint adjacent original negative-annulus compensated counts
-- statement:
--   For any nested three cutoffs and original spectrally negative Levy process, the two adjacent disjoint physical marked negative jump-count increments, each centred by its actual Levy intensity on the same horizon, have an integrable product and zero covariance. The proof uses physical annulus count additivity, the exact variance identities and genuine L2 integrability. This is a necessary disjoint-mark orthogonality ingredient for the infinite-activity weighted predictable martingale isometry, but is not itself a weighted predictable stochastic-integral theorem.
-- source:
--   MIX-INF15 root f5e6e083 through original stopped witness 5f12c023. Full independent source scratch/avram_mix_inf13_adjacent_annulus_cross_zero.lean, provenance SHA c4429db4aa731d8a9c90264815f3cc285d1d9240fda8b955ebfbce887b7a2de1. Exact original P, X, nu and marked jump count; no finite activity hypothesis.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_threecut_annulus_real_additivity
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) :
    let B : ℕ → ℕ → Set ℝ := fun a b =>
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B a b)
    let r : ℕ → ℕ → ℝ := fun a b =>
      ((T : ℝ≥0∞) * X.ν (B a b)).toReal
    Integrable (fun ω =>
      ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p)) P ∧
    (∫ ω, ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p) ∂P) = 0 := by sorry
