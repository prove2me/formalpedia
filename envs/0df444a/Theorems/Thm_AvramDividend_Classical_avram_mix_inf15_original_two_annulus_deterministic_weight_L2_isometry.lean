-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_two_annulus_deterministic_weight_L2_isometry
-- name    : AvramDividend.Classical.avram_mix_inf15_original_two_annulus_deterministic_weight_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:44:20.874699+00:00
-- url     : https://prove2.me/theorems/8177afb0-e8e6-4c56-a782-f8fc43152eb6
-- title:
--   Exact physical two-annulus deterministic-mark compensated L2 isometry
-- statement:
--   For two adjacent disjoint original negative jump-mark annuli, any deterministic real coefficients a and b yield a centred weighted count sum whose square is integrable and whose expected square is a² times the first annulus Levy intensity plus b² times the second. The proof uses genuine variance and disjoint-annulus covariance zero on original P. This is a finite simple-mark L2 brick, not yet the full stochastic predictable-mask isometry required by the mixed infinite-activity Ito witness.
-- source:
--   Original mixed-infinite physical annulus chain f5e6e083 -> 5f12c023; dependent on 6e234a3f and newly published exact adjacent covariance child. Deterministic mark step will feed finite-simple predictable marked grid isometry and L2 cutoff.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_original_two_annulus_deterministic_weight_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p)
    (a b : ℝ) :
    let B : ℕ → ℕ → Set ℝ := fun i j =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i j)
    let r : ℕ → ℕ → ℝ := fun i j =>
      ((T : ℝ≥0∞) * X.ν (B i j)).toReal
    let Y : Ω → ℝ := fun ω => (N n m ω).toReal - r n m
    let Z : Ω → ℝ := fun ω => (N m p ω).toReal - r m p
    Integrable (fun ω => (a * Y ω + b * Z ω) ^ 2) P ∧
      (∫ ω, (a * Y ω + b * Z ω) ^ 2 ∂P) =
        a ^ 2 * r n m + b ^ 2 * r m p := by sorry
