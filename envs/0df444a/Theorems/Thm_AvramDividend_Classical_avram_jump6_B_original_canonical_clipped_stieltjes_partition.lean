-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_clipped_stieltjes_partition
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:39:49.827049+00:00
-- url     : https://prove2.me/theorems/0f490725-c535-4d92-b97c-81dfbef53e89
-- title:
--   Original canonical physical stopped-grid half-open Stieltjes cash exact partition
-- statement:
--   For the original nondecreasing dividend Stieltjes measure on a real physical stopped grid, the sum of discounted cash integrals over every clipped half-open cell equals the exact discounted cash integral over the union, even after intersecting with an arbitrary measurable payment-time mask S. This uses the existing Proved original clipped grid monotonicity de2b51bf and masked Ioc partition b82bd6d9, preserving the original stopped endpoint and actual payment measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    (∑ i ∈ Finset.range m,
      ∫⁻ r in S ∩ Ioc (v i : ℝ) (v (i+1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) =
      (∫⁻ r in S ∩ Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) := by sorry
