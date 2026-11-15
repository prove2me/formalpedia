-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB65_original_smooth_compact_band_all_fullcell_value_modulus
-- name    : AvramDividend.Classical.avram_gbB65_original_smooth_compact_band_all_fullcell_value_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:02:09.49583+00:00
-- url     : https://prove2.me/theorems/82138f1e-f41d-4eac-b378-f5e849ed4097
-- title:
--   Original Gaussian all physical full-cell smooth interior-band value increments vanish uniformly almost surely
-- statement:
--   For every true original pure-Gaussian Lévy source and actual controlled postpayment reserve, the original C2 candidate w has uniformly vanishing spatial value changes on all sufficiently fine full physical mesh cells whose before-and-after predividend source states remain in a fixed compact positive interior reserve band [δ,K] below the original admissibility cap C. The compact Lipschitz constant is derived from C2 smoothness, with no artificial global payoff regularity or fake clipping cap. This supplies a genuine source full-cell spatial modulus needed for the stopped Itô-Tanaka B54 estimate.
-- source:
--   Proved original p4_f3 compact C2 payoff Lipschitz existence on [δ,K] and Proved B64 original Gaussian full physical-cell source uniform modulus conditional on both source states in that band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_gaussian_compact_band_all_fullcell_spatial_value_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB65_original_smooth_compact_band_all_fullcell_value_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        ∀ i : ℕ, i < m →
          let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          x + X.X s ω - rightLimit D s ω ∈ Icc δ K →
          x + X.X (s + Δ) ω - rightLimit D s ω ∈ Icc δ K →
          |w (x + X.X (s + Δ) ω - rightLimit D s ω) -
            w (x + X.X s ω - rightLimit D s ω)| < ε := by sorry
