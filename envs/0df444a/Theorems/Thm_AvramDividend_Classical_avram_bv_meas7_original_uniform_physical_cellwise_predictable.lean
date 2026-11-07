-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_physical_cellwise_predictable
-- name    : AvramDividend.Classical.avram_bv_meas7_original_uniform_physical_cellwise_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:52:58.891845+00:00
-- url     : https://prove2.me/theorems/84befa90-4dce-4669-8f18-07b97c9ff3d7
-- title:
--   Every original physical grid cell has both centred jump increment and predictable stop mask
-- statement:
--   Under the original bounded-variation Lévy process X and original admissible dividend strategy D, there exists a strict-prefix uniform physical grid. On every active cell the original X.nu compensated jump-source increment between its literal adjacent endpoints is integrable and exactly mean-zero; using that same cell endpoint, the genuine ruin-stopped clock is bounded and a stopping time for the right-continuous filtration and its compact pre-reserve mask is predictable. The theorem thus gives both stochastic and filtration certificates on each physical cell of the same original grid.
-- source:
--   Specialise Proved original physical uniform grid c527d1bc, Proved original two-clock compensated source 0f48f2b4 to every pair u(n,i),u(n,i+1), and Proved original ruin-stopped compact previsible mask 7759e9e1 at the literal right endpoint of that same cell. Extract the admissible strategy's dividend-strategy component hD.1.1. This removes publication-time dependency on an outstanding child, and introduces no stochastic assumptions.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_compact_stopped_clock_increment_centered
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_uniform_physical_cellwise_predictable
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
