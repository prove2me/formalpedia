-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_given_uniform_grid_centred_compensator
-- name    : AvramDividend.Classical.avram_p3_comp8_original_given_uniform_grid_centred_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:19:33.890708+00:00
-- url     : https://prove2.me/theorems/f3c89804-9fab-4e2a-bd71-55eb01618a58
-- title:
--   Original given uniform grid has centred integrable intrinsic stopped-jump compensator
-- statement:
--   Transfers the BV-MEAS7 compensated-jump martingale on its constructed uniform physical grid to the exact pre-specified original u used by 4044d709. Its stopped cutoff, left limits, jump measure and stochastic process are unchanged. Requires compact interior bands; passing to the full unlocalised process remains separate.
-- source:
--   Proved a08ce531 and b832785c; P3-COMP8 source-bound centred-grid transfer pending publication. Its result is a non-circular localised stochastic mean-zero certificate; the vanishing original positive payoff deficit remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_given_uniform_grid_centred_compensator
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
            {s : ℝ≥0 | 0 < s ∧
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s ≠ 0}).map
            (fun s : ℝ≥0 => (s,
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1)) (fun i => M (u n (i + 1)) ω - M (u n i) ω)) ∂P) = 0 := by sorry
