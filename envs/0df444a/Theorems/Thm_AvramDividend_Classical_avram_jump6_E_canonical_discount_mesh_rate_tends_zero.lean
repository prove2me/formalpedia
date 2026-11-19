-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_canonical_discount_mesh_rate_tends_zero
-- name    : AvramDividend.Classical.avram_jump6_E_canonical_discount_mesh_rate_tends_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:21:45.510999+00:00
-- url     : https://prove2.me/theorems/f38c8691-255c-4184-9380-7a38433cac05
-- title:
--   Canonical discounted Stieltjes mesh scalar error q/(j+1) times fixed stopped dividend variation tends to zero
-- statement:
--   Prove the fixed-path deterministic real scalar discount error q/(j+1)*V converges to zero for any real q,V along canonical j→∞. The physical Stieltjes source error in the original Avram mixed-noise infinite jump scheme is controlled by precisely this term when finite-grid cell mass/secant estimates hold. Reuse the pinned Mathlib lemma tendsto_one_div_add_atTop_nhds_zero_nat and scalar multiplication. This is the independent genuine proven analytic transfer, not an unproven stochastic approximation.

import Mathlib
open Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_E_canonical_discount_mesh_rate_tends_zero
    (q V : ℝ) :
    Tendsto (fun j : ℕ => q * (1 / (((j : ℝ) + 1))) * V)
      atTop (𝓝 (0 : ℝ)) := by sorry
