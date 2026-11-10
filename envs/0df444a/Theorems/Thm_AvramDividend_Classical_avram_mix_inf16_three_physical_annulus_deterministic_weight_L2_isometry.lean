-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf16_three_physical_annulus_deterministic_weight_L2_isometry
-- name    : AvramDividend.Classical.avram_mix_inf16_three_physical_annulus_deterministic_weight_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:29:26.943751+00:00
-- url     : https://prove2.me/theorems/4f7b6a79-389e-44d7-ba7b-8c7705ed1977
-- title:
--   Original physical three-annulus deterministic-mark compensated L2 isometry
-- statement:
--   For three consecutive disjoint original negative-jump-mark annuli, the compensated physical count with any three deterministic real weights has an integrable square with exact expected square equal to the sum of the squared weights multiplied by each Levy intensity. Adjacent orthogonality and separated orthogonality are both used. This is a finite-simple marked kernel brick; state-dependent predictable stochastic integrals still require separate proof.
-- source:
--   Root-connected marked jump L2 construction for mixed infinite-activity witness 5f12c023; Proved a13593f2 adjacent, Proved 9c325a05 separated, Proved 6e234a3f variance.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf16_three_physical_annulus_deterministic_weight_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q)
    (a b c : ℝ) :
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
    let Y : ℕ → ℕ → Ω → ℝ := fun i j ω =>
      (N i j ω).toReal - r i j
    Integrable (fun ω =>
      (a * Y n m ω + b * Y m p ω + c * Y p q ω) ^ 2) P ∧
    (∫ ω, (a * Y n m ω + b * Y m p ω + c * Y p q ω) ^ 2 ∂P) =
      a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q := by sorry
