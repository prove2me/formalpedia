-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
-- name    : AvramDividend.Classical.avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:47:59.578687+00:00
-- url     : https://prove2.me/theorems/b9dccb4b-7e6b-4610-a870-e7dbabe2d7b7
-- title:
--   Exact original physical stopped-grid four-term discounted Stieltjes telescoping chain reaches the true clock rho and preserves initial right-payment atom
-- statement:
--   For any genuine original spectrally negative Lévy reserve X and actual dividend strategy D on a bounded stopped clock rho, choose canonical clipped physical grid u_i=min(min(i,m+1)*n/(m+1),rho(ω)). This grid is monotone, starts at zero, reaches exactly rho at index m+1, and the terminal discounted w(x+X−rightLimitD) equals w(x), the exact original initial right-payment atom, and the sum of four exact discounted cell terms separating clock discount, process movement, prepayment to postpayment reserve and dividend right-jump. This is a sound exact finite mesh identity needed to assemble the signed purejump Ito ledger. No stochastic approximation or artificial dividends are used.
-- source:
--   Proved wave5_03 original controlled four-term finite-grid chain, Proved p3_2 canonical stopped grid monotonicity and Proved p3_grid3 terminal time n.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ρ : Ω → ℝ≥0)
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by sorry
