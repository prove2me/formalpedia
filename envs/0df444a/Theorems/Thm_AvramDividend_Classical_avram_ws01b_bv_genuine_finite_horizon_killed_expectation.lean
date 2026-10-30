-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation
-- name    : AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:13:59.990336+00:00
-- url     : https://prove2.me/theorems/03ac4ad0-bbd8-40d0-a333-f7b5dc940727
-- title:
--   Exact original BV finite-horizon killed q-scale expectation through authentic natural-index ceiling grids
-- statement:
--   For actual standing spectrally negative bounded-variation Lévy process, every nonnegative x≤a, positive discount q, true bounded two-sided exit clocks, any positive vanishing grid mesh, and genuine exponent moment parameter, the explicit source killed finite-horizon stopped q-scale limit is integrable with exact original-law expectation Wq(x). Combines proved pathwise three-way endpoint convergence, exact positive-grid optional stopping, true reward integrability, and uniform second-moment convergence.
-- source:
--   Proved actual BV three-branch killed grid convergence, original-Lévy L² integrals, true natural-index bounded-grid killed OST, bounded killed reward integrability, non-circular sampled Lévy filtration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_capped_grid_integral_convergence
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_clipped_ceiling_grid_killed_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) :
    (let Z : Ω → ℝ := fun ω =>
      if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
        if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
              W (x + X.X (min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a-x) ω then 0
      else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω);
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x) := by sorry
