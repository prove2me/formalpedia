-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_scale_origin_pos_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_root_scale_origin_pos_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T04:16:54.587821+00:00
-- url     : https://prove2.me/theorems/fc6b315a-4abb-4cb5-b39f-837f2962c6f0
-- title:
--   Root-based scale origin positivity without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive discount q, positive Laplace root φ, and genuine q-scale function W, the scale function is strictly positive at the origin, with no Standing assumption. Public bridge isolating the origin case of root scale positivity.
-- source:
--   Source-faithful isolation of the x=0 case of public parent AvramDividend.Classical.p2m81_bv_root_scale_pos_no_standing_public (33b910b1). The bridge v2 continuity argument (positivity on (0,∞) plus right-continuity) does not imply strict positivity at the limit and is mathematically invalid; the origin needs a genuine root renewal/Tauberian argument replaying bv_scale_origin_eq_inv_drift 973f7ca3 (proof 665ddae6, via Esscher geometric renewal bd5082fb) with the given root φ in place of bv_positive_esscher_root and root drift D1 in place of bv_standing_drift_pos. Supplies the origin disjunct for 33b910b1. No hypotheses weakened.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_root_scale_origin_pos_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    0 < W 0 := by sorry
