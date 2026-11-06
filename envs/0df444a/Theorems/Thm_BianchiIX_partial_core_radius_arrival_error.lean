-- Prove2me | Theorems.Thm_BianchiIX_partial_core_radius_arrival_error
-- name    : BianchiIX.partial_core_radius_arrival_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:28.703202+00:00
-- url     : https://prove2.me/theorems/f17a4455-04ab-41dd-984e-8d62ea48e95a
-- title:
--   Combining radial drift with the moving-wall arrival correction
-- statement:
--   Let $k\geq6$, $U,P\geq0$, $U+P\leq1$, $K\geq1$,
--   $0\leq s\leq1$. For real $q,r,X,dR,dU,dP,dz$, assume
--   $$|s-1|\leq8(U/k+P^2/k^2),\quad
--   |r-dR|\leq2(kU+P^2/k)|dz|,$$
--   $$X\leq k|dU|+2k^2U|dz|,$$
--   $$|q-r|\leq256\left[X/k+\frac{4K(U+P)}k
--   \bigl(|dR|+k|dU|+|dP|+(k^2U+P/k)|dz|\bigr)\right].$$
--   Then
--   $$|sq-dR|\leq4096K\left[|dU|+
--   \frac{(U+P)(|dR|+|dP|)}k+(kU+P^2/k)|dz|\right].$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreResponse.lean#L30-L99

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.partial_core_radius_arrival_error {k U P K s q r X dR dU dP dz : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hP : 0 ≤ P) (hsmall : U + P ≤ 1) (hK : 1 ≤ K)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hse : |s - 1| ≤ 8 * (U / k + P ^ 2 / k ^ 2))
    (hr : |r - dR| ≤ 2 * (k * U + P ^ 2 / k) * |dz|)
    (hX : X ≤ k * |dU| + 2 * k ^ 2 * U * |dz|)
    (hd : |q - r| ≤ 256 * (X / k + (U + P) *
      ((4 * K) * (|dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz|)) / k)) :
    |s * q - dR| ≤ 4096 * K *
      (|dU| + (U + P) * (|dR| + |dP|) / k + (k * U + P ^ 2 / k) * |dz|) := by sorry
