-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_scale_pos_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T04:03:47.77381+00:00
-- url     : https://prove2.me/theorems/33b910b1-d802-435b-8b3a-4c5717e7a258
-- title:
--   Root-based scale positivity without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive discount q, positive Laplace root φ, and genuine q-scale function W, the scale function is strictly positive at every nonnegative x, with no Standing assumption. Public bridge for grid integrability in the standing-free BV finite-horizon expectation.
-- source:
--   Public source-faithful extraction from public parent AvramDividend.Classical.p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing (f3582777-9357-4e66-a07d-7cb0a45dadf9) draft lines 56-85 (drift q ≤ φ·drift) plus 169-210 (positivity via 40da2a27 + right-continuity). Replaces private helper p2m81_bv_root_scale_pos_no_standing (job 40b65fef, request 719192e9) which cannot be imported by a public target (error 1795320183720607850-3). Supplies hWpos for by_contra grid integrability from Open OST db3e52be.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx0 : 0 ≤ x) :
    0 < W x := by sorry
