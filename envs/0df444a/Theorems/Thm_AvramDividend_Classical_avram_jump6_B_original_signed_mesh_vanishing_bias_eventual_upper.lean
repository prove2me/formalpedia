-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
-- name    : AvramDividend.Classical.avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:00:24.01918+00:00
-- url     : https://prove2.me/theorems/7bcf6876-af72-4436-9492-74cf4be009ad
-- title:
--   Original centred physical-grid source: vanishing Euler-bias signed eventual upper bound
-- statement:
--   If an actual finite physical-grid source splits exactly into a centred martingale term, a pathwise nonpositive HJB frozen-generator term and a deterministic mesh bias tending to zero, then uniformly across sample paths its source is eventually bounded by its martingale term plus arbitrary positive epsilon. This avoids needing pathwise generator Riemann convergence. It provides a sound one-sided route for the original Levy stopped expected-reward upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
    {Ω : Type*}
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω + bias j)
    (hQsign : ∀ j ω, Q j ω ≤ 0)
    (hBias : Tendsto bias atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ ω, Source j ω ≤ M j ω + ε := by sorry
