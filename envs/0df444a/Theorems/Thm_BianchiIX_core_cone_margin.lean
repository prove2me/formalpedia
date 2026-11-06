-- Prove2me | Theorems.Thm_BianchiIX_core_cone_margin
-- name    : BianchiIX.core_cone_margin
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T03:28:33.442025+00:00
-- url     : https://prove2.me/theorems/6ccbc6a8-6a24-4b95-afdb-57b5f09c15db
-- title:
--   A quantitative square-root cone margin from multiplier and radial estimates
-- statement:
--   Let $k\geq6$, $0\leq\varepsilon\leq1$,
--   $0\leq u,w\leq\varepsilon/k$, $|a|\leq\sqrt u$, and
--   $|b|\leq\sqrt w$. Put $Q=1+k|a|+|b|$. Suppose $R,A,B\geq0$ and
--   $$7R\sqrt\varepsilon,\ 38400A\sqrt\varepsilon,\
--   3B\sqrt\varepsilon\leq1/32,$$
--   $$0<m_U\leq e^{-k/40},\qquad0<m_W\leq e^{-1/(2k)},$$
--   $$|d_K-1|\leq R\bigl(|a|/k+(u+w)Q/k\bigr),$$
--   $$|\ell_U|\leq A\log(4k)Q,\qquad
--   |\ell_W|\leq B\log(4k)Q/k^2,$$
--   $$d_U=m_U(a+u\ell_U),\qquad d_W=m_W(b+w\ell_W).$$
--   Then $d_K>0$, $|d_K-1|\leq1/(32k)$, and
--   $$|d_U|\leq\left(1-\frac1{16k}\right)\sqrt{um_U}\,d_K,
--   \qquad |d_W|\leq\left(1-\frac1{16k}\right)\sqrt{wm_W}\,d_K.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCone.lean#L35-L147

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_cone_margin {k ε u w a b R A B mU mW lU lW dK dU dW : ℝ}
    (hk : 6 ≤ k) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmallR : 7 * R * Real.sqrt ε ≤ 1 / 32)
    (hsmallU : 38400 * A * Real.sqrt ε ≤ 1 / 32)
    (hsmallW : 3 * B * Real.sqrt ε ≤ 1 / 32)
    (hmU : 0 < mU ∧ mU ≤ Real.exp (-k / 40))
    (hmW : 0 < mW ∧ mW ≤ Real.exp (-1 / (2 * k)))
    (hrad : |dK - 1| ≤ R * (|a| / k + (u + w) * (1 + k * |a| + |b|) / k))
    (hlogU : |lU| ≤ A * Real.log (4 * k) * (1 + k * |a| + |b|))
    (hlogW : |lW| ≤ B * Real.log (4 * k) * (1 + k * |a| + |b|) / k ^ 2)
    (hdU : dU = mU * (a + u * lU)) (hdW : dW = mW * (b + w * lW)) :
    0 < dK ∧ |dK - 1| ≤ 1 / (32 * k) ∧
      |dU| ≤ (1 - 1 / (16 * k)) * Real.sqrt (u * mU) * dK ∧
      |dW| ≤ (1 - 1 / (16 * k)) * Real.sqrt (w * mW) * dK := by sorry
