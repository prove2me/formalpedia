-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
-- name    : AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:30:32.084185+00:00
-- url     : https://prove2.me/theorems/c17e6a0d-88fd-47b4-8f86-bcd5037e5cb5
-- title:
--   Original negative-annulus past count is orthogonal to later separated Borel marks
-- statement:
--   For the unchanged original Levy jump measure and original filtration, the past annulus count centred by the difference of its two full-cutoff expected rates is uncorrelated in real L1 with a later separated negative Borel count centred by its true Levi intensity. Derived by subtracting two Proved original full-cutoff/Borel cross-time covariance identities using the Proved physical nested cutoff count identity f0104cbc. This is the off-diagonal stochastic input for original annulus factorial moment 6ea0212e and physical mixed source isometry.
-- source:
--   MIX-SOURCE13 source-exact annulus off-time covariance; original same Ω/P/𝓕; no surrogate Poisson process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_borel_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((m : ℝ) + 1)))) :
    let K : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((i : ℝ) + 1))))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))))
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((i : ℝ) + 1))))).toReal
    let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - (r m - r n)) *
      ((F ω).toReal - q) ∂P) = 0 := by sorry
