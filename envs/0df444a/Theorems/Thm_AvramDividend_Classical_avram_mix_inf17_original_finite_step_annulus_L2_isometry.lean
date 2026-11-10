-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_original_finite_step_annulus_L2_isometry
-- name    : AvramDividend.Classical.avram_mix_inf17_original_finite_step_annulus_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:17:50.119194+00:00
-- url     : https://prove2.me/theorems/0af54511-8e42-4745-8fd2-6e70fd702ffd
-- title:
--   Original physical finite deterministic simple negative-mark compensated L2 isometry
-- statement:
--   For every finite ordered sequence of disjoint negative jump annuli of the same original Lévy process, an arbitrary finite deterministic scalar-simple mark weight gives a squared-integrable compensated count sum whose exact second moment is the sum of the weighted Lévy-rate variances. Derive with original annulus variance, original separated covariance and finite orthogonal-integral algebra. This is a finite simple-mark building block; further predictable random marks, infinite small-jump cutoff convergence, Gaussian residual and stopped cash source remain genuine obligations.
-- source:
--   Root-connected MIX-INFINITE original compensated-jump mark-step L2 programme, f5e6e083 via 5f12c023. Uses Proved 6e234a3f, 9c325a05 and 9c3483da; not an auxiliary Brownian or full stopped source claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf17_original_finite_step_annulus_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) (k : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
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
