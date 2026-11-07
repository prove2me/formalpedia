-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_positive_cap_uniform_source_predictable_auto
-- name    : AvramDividend.Classical.avram_bv_meas7_original_positive_cap_uniform_source_predictable_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:25:47.303914+00:00
-- url     : https://prove2.me/theorems/b7ad129f-7541-41c6-8c94-04367b888c24
-- title:
--   Original positive-cap uniform stopped jump source and predictable grid with automatic bands
-- statement:
--   Under the actual bounded-variation spectrally negative Levy process X and original admissible dividend strategy D, with strictly positive cap C, construct physical compact localisation bands a_n,b_n and one strict-prefix uniform stopped grid u simultaneously. For every n the original X.nu compensated source increment grid sum is integrable and has zero expectation, and its actual ruin-stopped endpoint is a bounded stopping time with predictable pre-reserve compact band mask. No externally assumed band sequences, stochastic martingale assumptions or equality-in-law substitutions.
-- source:
--   Combine Proved/public BV-MEAS7 positive-cap compact-band existence e642908b (using both finite/uncapped source theorems) and Proved/public original uniform stopped-grid source/predictability certificate 93ed08a7. This removes the deterministic band-existence instance left implicit in the source-to-physical-grid adapter. Full unlocalised passage and cash/Taylor residual remain separate.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_expanding_compact_bands_auto
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_grid_centered_predictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_positive_cap_uniform_source_predictable_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ) (hT : 0 < T) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) ∧
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
              {u : ℝ≥0 | 0 < u ∧
                X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') u)))
          (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
          (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
        let S : ℝ≥0 := u n (n + 1)
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        (Integrable (fun ω => Finset.sum (Finset.range (n + 1))
          (fun i => M (u n (i + 1)) ω - M (u n i) ω)) P ∧
         (∫ ω, (Finset.sum (Finset.range (n + 1))
          (fun i => M (u n (i + 1)) ω - M (u n i) ω)) ∂P) = 0) ∧
        ((∀ ω, τ ω ≤ S) ∧
         IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
         MeasurableSet[𝓕.rightCont.predictable] E ∧
         (∀ p ∈ E, Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
         (∀ p ∈ E, p.1 ≤ S)) := by sorry
