-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:37:50.42695+00:00
-- url     : https://prove2.me/theorems/31e87da4-7ba8-4052-bea1-4dd3e6741255
-- title:
--   Original physical mesh triangular pair mass tends to genuine squared Levy rate
-- statement:
--   For the actual original spectrally negative Levy process X and its own negative-band intensity ν_X(B), the triangular physical equal-mesh pair-weight expression converges in ENNReal to ((T ν_X(B))^2)/2. Assumes source band intensity finite. Combines two independently Proved source-X adapters into the exact source-mesh limit required for P4-F factorial moments; does not use equality in law or a synthetic Poisson point family.
-- source:
--   Existing Proved helper ee7d7d7b-0779-4d3d-86ad-abe1ca06d43b and Proved helper 35bbaf6a-c0b7-4c81-8716-fd3cf692f602, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    let a : ℝ := (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * a) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by sorry
