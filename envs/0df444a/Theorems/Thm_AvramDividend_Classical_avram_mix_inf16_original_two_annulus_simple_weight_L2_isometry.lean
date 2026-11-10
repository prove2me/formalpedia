-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
-- name    : AvramDividend.Classical.avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:30:05.472305+00:00
-- url     : https://prove2.me/theorems/64adfdbd-8bc9-47a3-a64b-7a14d23c1ddb
-- title:
--   Original physical compensated negative-annulus two-cell simple mark weight L2 isometry
-- statement:
--   For two disjoint ordered negative jump-mark annuli on the same original Lévy path, any constant-weighted linear combination of their centred physical counts has exactly the sum of the two weighted variances. This is a concrete two-cell simple-function basis for mark-weighted small-jump L2 isometry. Derive directly from original annulus exact variance and cross covariance, without auxiliary processes or unproved source assumptions.
-- source:
--   Root-connected mixed infinite-activity stopped martingale witness f5e6e083 via 5f12c023: physical marked-count simple-function orthogonality using Proved 6e234a3f and 9c325a05. Not a replacement for full predictable-mask isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q)
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
    let Y : ℕ → ℕ → Ω → ℝ := fun i j ω => (N i j ω).toReal - r i j
    Integrable (fun ω => (a * Y n m ω + b * Y p q ω) ^ 2) P ∧
      (∫ ω, (a * Y n m ω + b * Y p q ω) ^ 2 ∂P) =
        a ^ 2 * r n m + b ^ 2 * r p q := by sorry
