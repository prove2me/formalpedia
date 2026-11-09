-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_factorial_moment_exact
-- name    : AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_factorial_moment_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-08T23:14:11.696962+00:00
-- url     : https://prove2.me/theorems/6ea0212e-5dca-4086-9459-b51a194f926c
-- title:
--   Original annulus chronological factorial pair mean
-- statement:
--   For the literal original X.X point-jump count on the same Ω, P, and original filtration, the number of ordered distinct negative-annulus jump pairs has factorial expectation (T ν(B))². Derive via the existing original predictable mark compensation, physical chronological pair counting, and refinement. This sole missing stochastic premise plus Proved real first moment and MemLp 2 supplies exact annulus count variance 6e234a3f-568d-4eb5-a21c-b67b437bef4b. No assumed cross-mark independence, isometry, Gaussian replacement, or auxiliary Levy process.
-- source:
--   AVRAM MIX-SOURCE13 8 November 2026: unique missing original annulus factorial pair source behind 6e234a3f, for MIX-FIN13 and MIX-INF13.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_factorial_moment_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by sorry
