-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:45:08.407736+00:00
-- url     : https://prove2.me/theorems/0feecaa3-5fa6-4bf4-ad87-d61c64dd9dbe
-- title:
--   Original canonical physical stopped dividend discount oscillation controlled by total right-limit variation
-- statement:
--   The true original stopped canonical refining physical grid has discounted right-limit dividend mass oscillation at most q/(j+1) times its total right-limit dividend variation, pathwise, with arbitrary negative-jump activity and a nonzero Gaussian component allowed. Follows from Proved original general discount-mesh estimate b04aa727 and Proved clipped-grid cell widths de2b51bf. This is a quantitative ingredient for the exact closed-Iic cash-error limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i+1) : ℝ)))) *
      (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) ≤
      q * (Δ : ℝ) * (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by sorry
