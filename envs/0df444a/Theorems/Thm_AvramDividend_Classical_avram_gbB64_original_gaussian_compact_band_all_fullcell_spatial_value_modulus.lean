-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
-- name    : AvramDividend.Classical.avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:44:54.733208+00:00
-- url     : https://prove2.me/theorems/47d831b1-8010-48ab-a79a-ce30b936fbc8
-- title:
--   Original Gaussian full physical-cell caplinear potential increments uniformly vanish on every compact Lipschitz reserve band
-- statement:
--   For the original pure-Gaussian source X and actual dividend right-limit D, a test payoff V that is Lipschitz on a specified compact band has, for almost all original sample paths, uniformly small test-payoff changes across every physically full Gaussian mesh cell whenever both corresponding predividend-controlled spatial reserves remain in that compact band. This establishes the source-faithful compact-band spatial modulus used to prove the L1 Taylor remainder for B54 without requiring global Lipschitz continuity or artificial dividend admissibility at the interior clipping cap.
-- source:
--   Original zero-nu physical all-cell raw source uniform path modulus A409 and compact-band Lipschitz, applied to Y_i=x+X(s_i)-rightLimit D(s_i) and Z_i=x+X(s_i+Δ)-rightLimit D(s_i); rightLimit dividend cancels exactly from spatial increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a409_original_zerojump_all_fullcells_uniform_source_modulus
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (V : ℝ → ℝ)
    (lo hi L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi,
      |V v - V u| ≤ L * |v - u|)
    (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          x + X.X s ω - rightLimit D s ω ∈ Icc lo hi →
          x + X.X (s + Δ) ω - rightLimit D s ω ∈ Icc lo hi →
          |V (x + X.X (s + Δ) ω - rightLimit D s ω) -
            V (x + X.X s ω - rightLimit D s ω)| < ε := by sorry
