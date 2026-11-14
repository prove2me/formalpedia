-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
-- name    : AvramDividend.Classical.avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:49:52.409513+00:00
-- url     : https://prove2.me/theorems/bc02d2a4-3bb3-4c12-bf95-c5f0ce3162e7
-- title:
--   Original arbitrary cofinal positive spatial band lower endpoints necessarily converge to reserve zero with no nesting or mesh-rate restriction
-- statement:
--   Let C be the actual positive original dividend reserve cap and a_n,b_n be arbitrary supplied original positive interior spatial bands, each with [a_n/2,b_n] contained in the strict reserve interior (0,C), and assume the genuine cofinal coverage property: every fixed interior reserve y belongs to [a_n,b_n] for all sufficiently large n. Prove that the actual lower endpoints a_n tend to zero, regardless of band nesting or their rate relative to the simultaneous prescribed physical clock refinement. The first band provides a fixed interior reserve a_0; for each epsilon>0 take y=min(a_0,epsilon/2)>0 and strictly below C. Cofinal membership yields a_n≤y<epsilon eventually, while all a_n>0. This transfers the already Proved arbitrary shrinking-width negative Levy mark first-moment and physical drift estimates to the precise arbitrary a_n of the remaining original BVA96 C1 positive spatial error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
    (C : ℝ≥0∞) (hC : 0 < C)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by sorry
