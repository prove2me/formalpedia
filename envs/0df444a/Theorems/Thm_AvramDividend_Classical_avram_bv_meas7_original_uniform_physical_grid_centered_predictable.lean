-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_grid_centered_predictable
-- name    : AvramDividend.Classical.avram_bv_meas7_original_uniform_physical_grid_centered_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:37:42.810215+00:00
-- url     : https://prove2.me/theorems/93ed08a7-cfd5-4174-972e-7505115d7cf8
-- title:
--   Original single strict-prefix grid has centred compensated source and predictable ruin mask
-- statement:
--   Under the original bounded-variation spectrally negative Lévy process X, original admissible strategy D and compact interior bands, there is a single genuine physical uniform grid whose stopped X.nu compensated jump increments are integrable and mean zero and whose ruin-stopped pre-reserve mask is predictable for the same grid endpoint. The two independently constructed original-process grid witnesses are identified by the exact uniform widths; no proxy or stochastic assumptions are introduced.
-- source:
--   Proved source a08ce531 (original uniform stopped X.nu compensated increment mean zero); Proved endpoint predictable-mask source fa927f54; and proved uniqueness adapter b832785c transferring the finite endpoint clock between existential witnesses. The result discharges hMint and hMzero and supplies genuine predictable mask for the same stopped physical prefix used by the outstanding source/cash identity.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_grid_compensator_auto
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_grid_endpoint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_uniform_physical_grid_centered_predictable
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
    (T : ℝ) (hT : 0 < T) :
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
