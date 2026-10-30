-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_genuine_finite_horizon_killed_expectation
-- name    : AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:53:57.341338+00:00
-- url     : https://prove2.me/theorems/8dc0001a-c8dc-4a1a-ae64-5413fe1bb9df
-- title:
--   Original unbounded-variation source-Lévy finite-horizon killed scale expectation with all strict-passage branches
-- statement:
--   For the actual spectrally negative Levy process of unbounded variation, any nonnegative x<=a, finite horizon, vanishing positive mesh and positive q, with an available exponent moment parameter, the explicit finite-horizon continuously history-killed upper/lower first-passage payoff is integrable and its original-law expectation equals W(x). Include x=0 and cap/passage ties. Derive through authentic clipped-grid optional stopping, source L2-to-L1 integrability, pointwise all-path grid convergence and proven uniform second moment.
-- source:
--   Noncircular actual source UBV clipped ceiling-grid killed OST, source grid L2 integrability, source all-path killed grid limit, true masked-grid original-P integral convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_full_killed_ceiling_grid_reward_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_capped_grid_integral_convergence
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_integrable_from_square
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_genuine_finite_horizon_killed_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
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
