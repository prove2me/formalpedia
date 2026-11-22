-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_psi_quadratic_upper_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_psi_quadratic_upper_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:14:22.401014+00:00
-- url     : https://prove2.me/theorems/8b3585ed-e2b4-476c-aae1-0655a3745283
-- title:
--   Root-based quadratic Laplace upper bound without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive discount q and positive Laplace root φ, the Laplace exponent satisfies a quadratic upper bound ψθ - q ≤ (|drift|+|q|)(1+θ²) for all nonnegative θ, with no Standing assumption. Public bridge isolating the upper-bound half of scale positivity.
-- source:
--   Source-faithful extraction from public parent AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public (33b910b1) bridge /tmp/p2m81_scaleB_bridge.lean hquad block. Proves ψθ ≤ drift·θ via psi_upper_bound_by_compensated_small_jumps 85d8b8ec and exp(θy)-1≤0 for y<0 (using levy_compensated_jump_integrable_nonneg 1f95f376 and bv_small_negative_first_moment_integrable 2296f406), then ψθ-q ≤ |drift|θ+|q| ≤ (|drift|+|q|)(1+θ²). Reduces Child B bridge complexity (0.13 above cutoff) by isolating integral reasoning. Supplies hquadratic for 793f3b68. No hypotheses weakened.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_psi_quadratic_upper_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ - q ≤ (|X.drift| + |q|) * (1 + θ ^ 2) := by sorry
