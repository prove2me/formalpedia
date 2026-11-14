-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a110_original_gaussian_true_crossing_positive_expected_L1_from_source_and_compensator
-- name    : AvramDividend.Classical.avram_ga_a110_original_gaussian_true_crossing_positive_expected_L1_from_source_and_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:43:41.917079+00:00
-- url     : https://prove2.me/theorems/167378b3-6a81-46de-a660-92fff5ed0c45
-- title:
--   Original Gaussian actual clipped crossing cell has vanishing positive expected spatial error when source value displacement and compensator each vanish in L1
-- statement:
--   For the actual original Lévy source and dividend right limits, choose the randomly selected physical mesh index straddling the actual stopping clock. The positive part of the true clipped source generator residual is bounded by the discounted original stopped-source value difference and the absolute original full-clock compensation. Integrating yields positive expected L1 convergence from those two L1 estimates, without treating the crossing increment as an unclipped Gaussian or using a mesh-index count.
-- source:
--   Proved ga100 exact original source crossing positive bound and pinned Mathlib integral monotonicity, for physical clipped root b0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a110_original_gaussian_true_crossing_positive_expected_L1_from_source_and_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (n : ℕ)
    (i : ℕ → Ω → ℕ) (ρ : ℕ → Ω → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hs : ∀ (m : ℕ) (ω : Ω), let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ m ω)
    (hc : ∀ (m : ℕ) (ω : Ω), let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ m ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      |Real.exp (-(q * (ρ m ω : ℝ)))| *
        |w ((x + X.X s ω - rightLimit D s ω) +
          (X.X (ρ m ω) ω - X.X s ω)) -
          w (x + X.X s ω - rightLimit D s ω)|
    let B : ℕ → Ω → ℝ := fun m ω => |H m ω|
    let F : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k =>
        min ((k : ℝ≥0) * Δ) (ρ m ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t =>
        x + X.X t ω - rightLimit D t ω
      max (E (v (i m ω + 1)) *
        (w (x + X.X (v (i m ω + 1)) ω -
          rightLimit D (v (i m ω)) ω) -
          w (Y (v (i m ω)))) - H m ω) 0
    (∀ m, Integrable (A m) P) →
    (∀ m, Integrable (B m) P) →
    (∀ m, Integrable (F m) P) →
    Tendsto (fun m => ∫ ω, A m ω ∂P) atTop (𝓝 (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, B m ω ∂P) atTop (𝓝 (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
