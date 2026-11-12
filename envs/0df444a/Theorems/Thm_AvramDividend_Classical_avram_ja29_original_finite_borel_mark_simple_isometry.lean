-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja29_original_finite_borel_mark_simple_isometry
-- name    : AvramDividend.Classical.avram_ja29_original_finite_borel_mark_simple_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:00:23.887054+00:00
-- url     : https://prove2.me/theorems/901a7750-249f-4c9d-b98a-b9a98d0788ec
-- title:
--   Finite disjoint original Borel-mark simple-weight isometry from genuine physical cell moments
-- statement:
--   For disjoint measurable Borel mark cells in the original Levy jump measure, exact diagonal Poisson count variance and zero off-diagonal covariance imply the weighted finite simple-mark stochastic isometry. The source is the actual pathwise jump count; all physical moment premises remain explicit. Intended as an intermediate in proving bounded measurable mark moments by simple approximation.
-- source:
--   Proved generic finite weighted L2 moments theorem 99af255d; original marked count moments in 6e234a3f and 1279879b require Borel-cell extensions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja29_original_finite_borel_mark_simple_isometry
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    (∀ i ∈ F, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i) →
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) →
    Integrable (fun ω => (∑ i ∈ F, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ F, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ F, (a i) ^ 2 * r i := by sorry
