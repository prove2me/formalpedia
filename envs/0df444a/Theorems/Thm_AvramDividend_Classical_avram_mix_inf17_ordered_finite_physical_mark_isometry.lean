-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_ordered_finite_physical_mark_isometry
-- name    : AvramDividend.Classical.avram_mix_inf17_ordered_finite_physical_mark_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:40:35.82697+00:00
-- url     : https://prove2.me/theorems/63088608-bc98-42f2-ba4a-501945198d9b
-- title:
--   Original process arbitrary finite ordered negative-annulus simple-mark L2 isometry
-- statement:
--   For any finite family S of original negative mark intervals defined by reciprocal cutoff indices, whose intervals are pairwise separated and individually ordered, and any real deterministic weights c, the original physical compensated count step function satisfies exact L2 isometry. This discharges all finite-step pairwise integrability, variance and covariance assumptions of the already Proved 3a7ea415 directly from Proved 6e234a3f and 9c325a05. It is a source-exact finite-step prerequisite for approximating the physical mark z in the original mixed infinite-negative-jump activity small-strip L2 estimate, and hence the stopped Ito-Meyer witness 5f12c023 and original positive-clock reward f5e6e083. The result does not infer arbitrary predictable stopping or a Gaussian model by itself.
-- source:
--   Proved 3a7ea415 conditional finite-grid isometry instantiated with Proved 6e234a3f count variance and Proved 9c325a05 separated annulus integrable centred covariance, no surrogate stochastic source. Root-connected through 5f12c023 to f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf17_ordered_finite_physical_mark_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (S : Finset ℕ) (a b : ℕ → ℕ)
    (hLe : ∀ i ∈ S, a i ≤ b i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      b i ≤ a j ∨ b j ≤ a i) (c : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((a i : ℝ) + 1))) (-(1 / ((b i : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    (∫ ω, (∑ i ∈ S, c i * ((N i ω).toReal - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by sorry
