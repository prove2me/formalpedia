-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_real_stieltjes_discount_quadrature
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_real_stieltjes_discount_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:38:39.464353+00:00
-- url     : https://prove2.me/theorems/b874aeee-9594-4beb-a50f-48cb98b20bd4
-- title:
--   Original canonical physical right-end discounted Stieltjes cash quadrature with exact width error
-- statement:
--   For the genuine dividend Stieltjes measure of any original admissible filtered dividend strategy, the finite physical right-end discounted Riemann-Stieltjes cash sum is bounded above by the true integral over the same cells, and its gap is bounded by q/(j+1) times the total cell dividend mass. The clipped grid uses true stopped time t and a canonical step 1/(j+1), with actual exact dividend measure and no jump-activity assumption. Derive automatically from the two existing Proved theorems ad16e2af and de2b51bf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_canonical_real_stieltjes_discount_quadrature
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    let μ := dividendMeasure D ω
    (∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
      μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) ≤
      (∑ i ∈ Finset.range m, ∫⁻ r in Ioc (v i : ℝ) (v (i+1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ∧
    (∑ i ∈ Finset.range m, ∫⁻ r in Ioc (v i : ℝ) (v (i+1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ≤
      (∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
        μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) +
      ENNReal.ofReal (q * (Δ : ℝ)) *
        (∑ i ∈ Finset.range m, μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) := by sorry
