-- Prove2me | Theorems.Thm_BianchiIX_abs_slope_right_le_of_damping
-- name    : BianchiIX.abs_slope_right_le_of_damping
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:54:14.371201+00:00
-- url     : https://prove2.me/theorems/60ec15cb-703a-422c-9730-a8891fe293ab
-- title:
--   A scalar damping term contributes no positive absolute-value slope
-- statement:
--   Suppose $f:\mathbb R\to\mathbb R$ has derivative
--   $df(t)+g$ at $t$, where $d\leq0$ and $|g|\leq B<R$.
--   For all $s>t$ sufficiently near $t$,
--   $$\frac{|f(s)|-|f(t)|}{s-t}<R.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/DampedForcing.lean#L10-L43

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.abs_slope_right_le_of_damping {f : ℝ → ℝ} {t d g B r : ℝ}
    (hf : HasDerivAt f (d * f t + g) t) (hd : d ≤ 0) (hg : |g| ≤ B) (hr : B < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (|f s| - |f t|) < r := by sorry
