-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_exp_quotient_signed
-- name    : AvramDividend.Classical.avram_ja18g_original_large_negative_exp_quotient_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:41:15.302207+00:00
-- url     : https://prove2.me/theorems/4f5957f4-f50a-4bad-995b-52f68aa23ebf
-- title:
--   Negative large-mark Laplace quotient tends to signed first moment
-- statement:
--   For original ν with finite negative-large first moment established from Standing and finite jump activity, the quotient (∫_{z≤-1}(e^{θz}-1)ν(dz))/θ tends to ∫_{z≤-1}zν(dz) as θ↓0. Use scalar exponential right slope and dominated convergence bounded by |z| on negative marks, with existing Proved first-moment helper. No unjustified first moments outside the stated finite-activity conditions.
-- source:
--   J-A18 deterministic original Lévy-Khintchine large-negative derivative

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_large_negative_exp_quotient_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Filter.Tendsto
      (fun θ : ℝ =>
        (∫ z in Iic (-1 : ℝ), Real.exp (θ * z) - 1 ∂X.ν) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ z in Iic (-1 : ℝ), z ∂X.ν)) := by sorry
