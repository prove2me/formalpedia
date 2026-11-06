-- Prove2me | Theorems.Thm_BianchiIX_core_radius_arrival_error
-- name    : BianchiIX.core_radius_arrival_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:26:41.138701+00:00
-- url     : https://prove2.me/theorems/9047a489-8302-4395-860f-0a12263ab29b
-- title:
--   Combining radial drift with the entrance and moving-exit corrections
-- statement:
--   Let all variables be real. Suppose $k\geq6$,
--   $U,W\geq0$, $W\leq k$, $|v_0|\leq Q_0$, and $0\leq s\leq1$.
--   Assume
--   $$|s-1|\leq8(U/k+W^2/k^2),\qquad
--   |r-v_0|\leq4(U/k+W^2/k^2)|v_0|,$$
--   $$X\leq k|v_1|+4kU|v_0|,\qquad
--   |q-r|\leq256\left(X/k^2+(U+W)(2KQ_0)/k\right).$$
--   Then
--   $$|sq-v_0|\leq256|v_1|/k+(1040+512K)(U+W)Q_0/k.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/RadialError.lean#L15-L40

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_radius_arrival_error {k U W K Q₀ s q r X v₀ v₁ : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hW : 0 ≤ W) (hWk : W ≤ k)
    (hQ : |v₀| ≤ Q₀) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hse : |s - 1| ≤ 8 * (U / k + W ^ 2 / k ^ 2))
    (hr : |r - v₀| ≤ 4 * (U / k + W ^ 2 / k ^ 2) * |v₀|)
    (hX : X ≤ k * |v₁| + 4 * k * U * |v₀|)
    (hd : |q - r| ≤ 256 * (X / k ^ 2 + (U + W) * ((2 * K) * Q₀) / k)) :
    |s * q - v₀| ≤ 256 * |v₁| / k + (1040 + 512 * K) * (U + W) * Q₀ / k := by sorry
