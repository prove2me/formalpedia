-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise20_original_gaussian_residual_limit_count_bound
-- name    : AvramDividend.Classical.avram_anoise20_original_gaussian_residual_limit_count_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:31:02.51088+00:00
-- url     : https://prove2.me/theorems/fae860dd-a79e-4301-aa99-d2fce0c4a00b
-- title:
--   Original Gaussian limit residual error dominated by physical finite jump count
-- statement:
--   For the physical same-omega Gaussian residual limit R, its approximation error at finite cutoff n is bounded pathwise by one over n+1 times the total original negative-jump count plus source rate, provided the physical cutoff converges on that trajectory. No independent auxiliary process or large-jump absolute moment is needed.
-- source:
--   Direct limit of Proved a.e physical finite-count cutoff error 1b696ff5; this yields quantitative L2 convergence via original negative count quadratic bound a6562a4d, feeding original Gaussian martingale and bracket obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise20_original_gaussian_residual_limit_count_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (ω : Ω)
    (hRsource : Tendsto
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
      atTop (nhds (R T ω)))
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    |R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (1 / ((n : ℝ) + 1)) * (N.toReal + A) := by sorry
