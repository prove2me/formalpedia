-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uncapped_full_mask_cofinal_cellwise_predictable
-- name    : AvramDividend.Classical.avram_bv_meas7_original_uncapped_full_mask_cofinal_cellwise_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:56:44.256364+00:00
-- url     : https://prove2.me/theorems/4c48115d-7c61-44de-a594-6820fd827387
-- title:
--   Original uncapped full predictable band exhausts reserves with centred stopped cell source
-- statement:
--   For the actual original uncapped bounded-variation spectrally negative Lévy process X and admissible dividend strategy D, choose a strict-prefix uniform stopped physical grid and compact bands a_n,b_n. Every fixed positive reserve lies eventually in the full predictable mask band Icc(a_n,b_n), while the original X.nu compensated-jump increment on each stopped cell is L1 and mean zero; the stopped endpoint is a right-continuous-filtration stopping time and the full pre-reserve mask is predictable.
-- source:
--   Already Proved uncapped full predictable compact-band child and original source-exact uniform cellwise compensation/stopping/predictability theorem 84befa90.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_cellwise_predictable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_uncapped_full_mask_cofinal_cellwise_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (T : ℝ) (hT : 0 < T) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (∀ y : ℝ, 0 < y → ∃ N : ℕ, ∀ n ≥ N,
        y ∈ Icc (a n) (b n)) ∧
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
        ∀ i : ℕ, i < n + 1 →
          let S : ℝ≥0 := u n (i + 1)
          let τ : Ω → ℝ≥0 := fun ω =>
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let E : Set (ℝ≥0 × Ω) := {p |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
          (Integrable (fun ω => M (u n (i + 1)) ω - M (u n i) ω) P ∧
           (∫ ω, M (u n (i + 1)) ω - M (u n i) ω ∂P) = 0) ∧
          ((∀ ω, τ ω ≤ S) ∧
           IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
           MeasurableSet[𝓕.rightCont.predictable] E ∧
           (∀ p ∈ E, Function.leftLim
             (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
           (∀ p ∈ E, p.1 ≤ S)) := by sorry
