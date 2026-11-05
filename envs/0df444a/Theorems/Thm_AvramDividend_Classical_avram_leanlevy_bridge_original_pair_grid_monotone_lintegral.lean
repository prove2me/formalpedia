-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_pair_grid_monotone_lintegral
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_pair_grid_monotone_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:07:02.290622+00:00
-- url     : https://prove2.me/theorems/92020479-ca35-4c51-8a11-1a3e1e5365fa
-- title:
--   Original chronological negative-band pair expectation from monotone exhaustive physical grids
-- statement:
--   For the actual original spectrally negative Levy path and the literal finite set of its negative-band jump times, let G_m be a measurable increasing family of physically detected chronological pair sets, each a subset of the source ordered pairs and eventually exactly equal to them. Then monotone convergence identifies the full ENNReal expected source pair count with the supremum of the finite-grid expected pair counts. This is the analytic grid-to-full second-factorial-moment bridge, conditional only on explicit pathwise grid exhaustion and finite-grid means; it preserves the original probability space, X and filtration.
-- source:
--   Pinned MeasureTheory.lintegral_iSup signature, accepted P2-E original grid pair mean 77b37394, accepted original cross-window expectation a8adacce, open exact full pair target d938e9a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_pair_grid_monotone_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω, F ω =
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (G : ℕ → Ω → Finset (ℝ≥0 × ℝ≥0))
    (hSub : ∀ m ω, G m ω ⊆
      (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMono : ∀ m k, m ≤ k → ∀ ω, G m ω ⊆ G k ω)
    (hStop : ∀ ω, ∃ N, ∀ m ≥ N,
      G m ω = (F ω ×ˢ F ω).filter (fun p => p.1 < p.2))
    (hMeas : ∀ m, Measurable
      (fun ω => ((G m ω).card : ℝ≥0∞)))
    (A : ℕ → ℝ≥0∞)
    (hMean : ∀ m, (∫⁻ ω, ((G m ω).card : ℝ≥0∞) ∂P) = A m) :
    (∫⁻ ω, (((F ω ×ˢ F ω).filter
      (fun p => p.1 < p.2)).card : ℝ≥0∞) ∂P) =
      ⨆ m, A m := by sorry
