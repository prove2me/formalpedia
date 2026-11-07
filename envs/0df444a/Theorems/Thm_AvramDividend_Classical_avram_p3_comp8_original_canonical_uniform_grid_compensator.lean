-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_uniform_grid_compensator
-- name    : AvramDividend.Classical.avram_p3_comp8_original_canonical_uniform_grid_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:21:10.990185+00:00
-- url     : https://prove2.me/theorems/2c5ce887-cf3b-4554-a6d1-1c7e7c36d4ac
-- title:
--   Canonical original uniform grid carries its exact centred stopped-jump compensator
-- statement:
--   Under the original 4044d709 uniform-grid data, the same stopped compensated intrinsic Levy jump integral is L1 and mean-zero on the precise u-grid for each compact interior source band. The uniform cell width required by the Proved source theorem is derived algebraically from huniform. No cash/HJB claim is assumed.
-- source:
--   Original 4044d709 exact hgrid/huniform. Direct import of Proved P3-COMP8 f3c89804; all stochastic data unchanged. This is the grid-shape bridge, not full payoff closure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_given_uniform_grid_centred_compensator
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_canonical_uniform_grid_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n : ℕ,
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
        let τ : Ω → ℝ≥0 := fun ω' =>
          (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if p.1 ∈ E ∧ p.2 < 0 then
            Real.exp (-(q * (p.1.1 : ℝ))) *
              (w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
               w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
          else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
          ((Measure.count.restrict
            {s : ℝ≥0 | 0 < s ∧
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s ≠ 0}).map
            (fun s : ℝ≥0 => (s,
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)) ∂P) = 0 := by sorry
