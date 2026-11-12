-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_exponent_right_slope_triplet
-- name    : AvramDividend.Classical.avram_ja18g_original_levy_exponent_right_slope_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:38:32.354948+00:00
-- url     : https://prove2.me/theorems/81b9a427-3716-4e81-9aac-e4388caf6374
-- title:
--   Original Lévy-Khintchine exponent has its finite-activity triplet right derivative
-- statement:
--   As θ↓0, ψ_X(θ)/θ tends to c plus the signed large-negative Lévy mark first moment. Prove from the original Lévy-Khintchine integral split, the small compensated jump remainder O(θ), finite Gaussian θ² term, and large negative jump dominated convergence using the already Proved first absolute moment of ν on Iic(-1). Do not assume a large moment beyond Standing.
-- source:
--   J-A18 deterministic exponent differentiability step

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_levy_exponent_right_slope_triplet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν))) := by sorry
