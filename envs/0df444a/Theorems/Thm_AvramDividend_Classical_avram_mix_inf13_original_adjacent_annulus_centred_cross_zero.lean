-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_adjacent_annulus_centred_cross_zero
-- name    : AvramDividend.Classical.avram_mix_inf13_original_adjacent_annulus_centred_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:33:16.714872+00:00
-- url     : https://prove2.me/theorems/2082a156-1eab-475f-9f2e-e710b797e3e2
-- title:
--   Original adjacent negative-annulus compensated physical counts have zero cross moment
-- statement:
--   For the original spectrally negative Levy process on its given sample space and filtration, at every finite T and ordered reciprocal cutoffs n≤m≤p, the product of compensated physical counts of the disjoint adjacent annuli (n,m] and (m,p] is integrable, and its expectation is zero. This follows from original real annulus count additivity 278f17b6, exact physical centred count variances 6e234a3f and Levy rate additivity 832d1bcb via polarization. It discharges the equal-horizon cross-moment input to constructing the physical marked-annulus L2 isometry for f5e6e083. No detached Gaussian model or first absolute jump moment is assumed.
-- source:
--   Direct original-process prerequisite for physical small jump isometry and mixed-infinite stopped reward target f5e6e083; Proved 278f17b6, 6e234a3f, 832d1bcb, 963870c8.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf13_original_adjacent_annulus_centred_cross_zero
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
