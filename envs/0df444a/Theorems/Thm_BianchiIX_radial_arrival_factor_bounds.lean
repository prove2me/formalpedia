-- Prove2me | Theorems.Thm_BianchiIX_radial_arrival_factor_bounds
-- name    : BianchiIX.radial_arrival_factor_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:52:59.206095+00:00
-- url     : https://prove2.me/theorems/a875ebc5-0408-40a2-900f-b0dbe8d10f00
-- title:
--   The radial arrival factor is positive and at most one
-- statement:
--   For real $r,c,f$ with $r>0$, $c\leq-1/2$, and $f\leq0$,
--   $$c+f/r<0,\qquad 0<\frac c{c+f/r}\leq1,\qquad
--   \left|\frac c{c+f/r}-1\right|\leq\frac{2|f|}{r}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/RadialArrival.lean#L10-L28

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.radial_arrival_factor_bounds {r c f : ℝ} (hr : 0 < r) (hc : c ≤ -1 / 2) (hf : f ≤ 0) :
    c + f / r < 0 ∧ 0 < c / (c + f / r) ∧ c / (c + f / r) ≤ 1 ∧
      |c / (c + f / r) - 1| ≤ 2 * |f| / r := by sorry
