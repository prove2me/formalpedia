-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
-- name    : AvramDividend.Classical.avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:49:55.605374+00:00
-- url     : https://prove2.me/theorems/e52fd1ce-b2ac-4f09-9070-92a438d3d363
-- title:
--   Original arbitrary cofinal finite-cap interior upper spatial endpoints converge to the true cap regardless of nesting or rate
-- statement:
--   For the original dividend model with strictly positive finite cap C represented as ENNReal.ofReal L, L>0, take ANY prescribed original positive cofinal interior spatial bands a_n,b_n with a_n<=b_n and [a_n/2,b_n] strictly below the cap. Show that the actual upper endpoints b_n converge to L, independently of monotonicity, band nesting, chosen diagonals or simultaneous physical mesh rates. The strict interior inclusion ensures b_n<L every row. For any real e<L, take the interior reserve y=max(L/2,(e+L)/2), which is positive, below L and above e. Cofinal coverage forces b_n>=y>e eventually. Combined with b_n<L this proves the limit. It supplies the finite-cap localisation boundary condition needed in the source-exact infinite-activity bounded-variation C1 compensated spatial error proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
    (C : ℝ≥0∞) (L : ℝ) (hL : 0 < L)
    (hCL : C = ENNReal.ofReal L)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto b atTop (𝓝 L) := by sorry
