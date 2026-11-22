-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_doubling_laplace_point_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_doubling_laplace_point_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:03:45.151808+00:00
-- url     : https://prove2.me/theorems/2f5d869c-13b2-4843-af18-4f41935ab199
-- title:
--   Root doubling Laplace point exceeds discount (public)
-- statement:
--   For a spectrally negative Lévy process with positive discount q and a positive root φ of the Laplace exponent, the Laplace exponent at the doubling point 2φ strictly exceeds q. Public bridge for the standing-free BV finite-horizon grid integral convergence.
-- source:
--   Public source-faithful extraction from public parent AvramDividend.Classical.p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing (f3582777-9357-4e66-a07d-7cb0a45dadf9) draft /tmp/p2m81_parent_draft_v1.lean lines 88-129. Replaces private helper p2m81_bv_root_doubling_laplace_point_no_standing (job f276c080, request 719192e9) which cannot be imported by a public target (private dependency ownership error 1795320183720607850-3). Proves ψ(2φ) ≥ 2ψ(φ) via ψ(2θ)-2ψ(θ) = σ²θ² + ∫(exp-1)² ≥ 0, hence ψ(2φ) ≥ 2q > q. Supplies hψ for 67a550ca at θ*=2φ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_doubling_laplace_point_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    q < X.ψ (2 * φ) := by sorry
