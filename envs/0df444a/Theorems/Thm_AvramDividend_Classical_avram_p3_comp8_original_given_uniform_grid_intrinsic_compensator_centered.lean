-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_given_uniform_grid_intrinsic_compensator_centered
-- name    : AvramDividend.Classical.avram_p3_comp8_original_given_uniform_grid_intrinsic_compensator_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:18:07.167096+00:00
-- url     : https://prove2.me/theorems/cf6251d9-a42c-4b4c-af39-7832acca14d1
-- title:
--   Centred original stopped compensated negative-jump term transports onto every supplied physical uniform grid
-- statement:
--   For the original X,D and its actual negative jump counting measure, finite compensated stopped X.nu increments remain integrable and mean zero on an arbitrary supplied uniform physical mesh, with pointwise matched active cells. No unrelated grid or proxy martingale.
-- source:
--   Proved a08ce531 original source centered stopped compensator; Proved b832785c finite active-cell grid uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_grid_compensator_auto
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_given_uniform_grid_intrinsic_compensator_centered
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
    (hu0 : ∀ n, u n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) :
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
            {v : ℝ≥0 | 0 < v ∧
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
      (∫ ω, Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω) ∂P) = 0 := by sorry
