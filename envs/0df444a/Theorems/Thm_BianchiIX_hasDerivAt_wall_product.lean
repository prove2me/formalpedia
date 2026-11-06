-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_wall_product
-- name    : BianchiIX.hasDerivAt_wall_product
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:03:52.493742+00:00
-- url     : https://prove2.me/theorems/1b9b1b37-b38f-429e-88cf-cd86ab20c507
-- title:
--   Evolution of the product of the curvature walls
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $p,s,a,b,c$ be real functions. Suppose that at time $t$ the derivatives of
--   $a,b,c$ equal $r_1(p(t),s(t))a(t)$, $r_2(p(t),s(t))b(t)$,
--   and $r_3(p(t),s(t))c(t)$, respectively. Then
--   $$\frac{d}{dt}(abc)(t)=-3\bigl(p(t)^2+s(t)^2\bigr)a(t)b(t)c(t).$$
--   The identity supplies the evolution law for the wall product.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flow.lean#L65-L73

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

theorem BianchiIX.hasDerivAt_wall_product
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => a u * b u * c u)
      (-3 * shearSq (p t) (s t) * (a t * b t * c t)) t := by sorry
