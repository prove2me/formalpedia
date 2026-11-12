-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
-- name    : AvramDividend.Classical.avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:49:07.575796+00:00
-- url     : https://prove2.me/theorems/b0c87b9c-bb6b-42d1-acb3-7166143ce227
-- title:
--   Original strict inner-horizon and inclusive ruin mask stabilise off the ruin endpoint
-- statement:
--   At every fixed positive physical real time t<T away from the unique ruin instant, the original strict-inner-horizon and inclusive stopping mask 0<t<T−T/(n+2) ∧ ofReal(t)≤ruin eventually coincides with the limiting strict pre-ruin mask ofReal(t)<ruin. The inner horizons tend to T and strict/inclusive ruin predicates coincide off their equality time. This source-exact indicator stabilisation is a necessary a.e. convergence step for K in 7ccc2a1a.
-- source:
--   Original K integrand pointwise time-horizon/ruin mask convergence, supporting 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (hτ : ENNReal.ofReal t ≠ τ) :
    Filter.Eventually
      (fun n : ℕ =>
        (0 < t ∧ t < T - T / ((n : ℝ) + 2) ∧
          ENNReal.ofReal t ≤ τ) ↔
        (0 < t ∧ ENNReal.ofReal t < τ))
      Filter.atTop := by sorry
