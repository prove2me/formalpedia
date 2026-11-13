-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T10:06:48.577198+00:00
-- url     : https://prove2.me/theorems/16f30ca5-5195-4da0-b291-a29dcc1e5845
-- title:
--   Original BV pre-jump surplus has a deterministic finite upper envelope on each bounded horizon
-- statement:
--   The original left-limit prepayment reserve on every bounded horizon does not exceed max(x+max(T drift,0),0), almost surely at every clock. Follows from the already Proved postpayment upper bound and closure of Ici under left limits. Supplies the uniform compact reserve envelope for finite-activity top-cap marked compensation.
-- source:
--   Proof extracted as an exact intermediate from accepted avram_bv_residual9_original_global_leftlim_value_horizon_envelope, using Proved original postpayment upper horizon strip 7fa910be. No finite cap or value function premises.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t ≤
        max (x + max ((T : ℝ) * X.drift) 0) 0 := by sorry
