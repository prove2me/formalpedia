-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
-- name    : AvramDividend.Classical.avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T09:14:54.142233+00:00
-- url     : https://prove2.me/theorems/e83a2a28-41d5-4c23-bac5-c286068d7f8b
-- title:
--   Positive-cutoff physical residual independent of retained compensated negative jump noise, with retained L1
-- statement:
--   On the original probability space, at every positive horizon and positive cutoff, the cutoff Gaussian-plus-omitted-negative-jump residual is independent of the physically retained compensated negative-band jump noise. The retained noise is integrable. Disjoint Levy-Itô marked Poisson bands and the independent Brownian component justify the original source statement, unlike the false zero-cutoff residual/retained-band independence.
-- source:
--   Independent random measures on disjoint mark sets for the same original Levy process and source retained-band first moment; finite negative Levy activity. Downstream direct proof of strict positive-time source covariance orthogonality d754ce30.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      ProbabilityTheory.IndepFun R J P ∧ Integrable J P := by sorry
