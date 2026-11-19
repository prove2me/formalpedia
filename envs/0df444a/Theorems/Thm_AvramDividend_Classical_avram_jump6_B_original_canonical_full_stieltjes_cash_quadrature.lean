-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_full_stieltjes_cash_quadrature
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_full_stieltjes_cash_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:43:01.140138+00:00
-- url     : https://prove2.me/theorems/2622ff5f-138a-4ce1-a307-52ef83148361
-- title:
--   Original full stopped half-open Stieltjes discounted cash with explicit canonical grid error
-- statement:
--   Original dividend strategy physical-grid full-horizon true discounted cash integral over the stopped interval is sandwiched between the exact right-end Riemann-Stieltjes cash sum and that sum plus q times the grid width multiplied by total stopped dividend mass on the cells. Fuses three already Proved theorems: original canonical clipped width/monotonicity de2b51bf, finite mesh discounted error ad16e2af, and masked Ioc full interval partition b82bd6d9. No finite jump activity or process surrogates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_full_stieltjes_cash_quadrature
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    let μ := dividendMeasure D ω
    (∑ i ∈ Finset.range m,
      ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
        μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) ≤
      (∫⁻ r in Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ∧
    (∫⁻ r in Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ≤
      (∑ i ∈ Finset.range m,
        ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
          μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) +
      ENNReal.ofReal (q * (Δ : ℝ)) *
        (∑ i ∈ Finset.range m, μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) := by sorry
