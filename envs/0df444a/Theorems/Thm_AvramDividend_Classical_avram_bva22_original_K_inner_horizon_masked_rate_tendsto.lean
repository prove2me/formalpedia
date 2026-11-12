-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_inner_horizon_masked_rate_tendsto
-- name    : AvramDividend.Classical.avram_bva22_original_K_inner_horizon_masked_rate_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:34:24.533068+00:00
-- url     : https://prove2.me/theorems/e384d815-d075-4900-84ce-24f5e887d908
-- title:
--   Original K finite inner-horizon stopped mark rate converges pointwise away from ruin
-- statement:
--   The original K time integrand uses the exact positive inner-horizon mask 0<t<T-T/(n+2), inclusive ruin condition t≤τ and the original inclusive reserve cap. At every fixed 0<t<T distinct from ruin, the proved original strict-inner-horizon-ruin equivalence b0c87b9c makes this mask eventually identical to the limiting strict pre-ruin cap mask. The mark-rate coefficient v and reserve state b are held fixed in n, so eventually equality implies pointwise convergence. This is the K-side a.e. convergence required for the paired dominated-convergence proof of 7ccc2a1a.
-- source:
--   Exact original source K_n pointwise horizon mask convergence outside zero-volume ruin boundary for theorem 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_K_inner_horizon_masked_rate_tendsto
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (hτ : ENNReal.ofReal t ≠ τ) (b : ℝ)
    (C : ℝ≥0∞) (v : ℝ) :
    Tendsto (fun n : ℕ =>
      if 0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
        ENNReal.ofReal t ≤ τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)
      atTop (𝓝 (if 0 < t ∧ ENNReal.ofReal t < τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)) := by sorry
