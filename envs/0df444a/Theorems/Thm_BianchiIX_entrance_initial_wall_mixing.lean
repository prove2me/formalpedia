-- Prove2me | Theorems.Thm_BianchiIX_entrance_initial_wall_mixing
-- name    : BianchiIX.entrance_initial_wall_mixing
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:54:52.284207+00:00
-- url     : https://prove2.me/theorems/06cdfcaf-3403-45d3-8950-a975683712fc
-- title:
--   Initial wall mixing is controlled by two weighted amplitude columns
-- statement:
--   Let $k\geq1$, $\theta,u,v,w\in[0,1]$, and $X,Y\in\mathbb R$.
--   Then
--   $$(u|X|+w|Y|)\left(uv+\frac{uvw+\theta(vw)^2}{k^2}\right)
--   \leq3\bigl(uv|X|+(uvw+\theta(vw)^2)|Y|\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/EntranceVariationMixing.lean#L9-L47

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.entrance_initial_wall_mixing {k θ u v w X Y : ℝ}
    (hk : 1 ≤ k) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    (u * |X| + w * |Y|) * (u * v + (u * v * w + θ * (v * w) ^ 2) / k ^ 2) ≤
      3 * (u * v * |X| + (u * v * w + θ * (v * w) ^ 2) * |Y|) := by sorry
