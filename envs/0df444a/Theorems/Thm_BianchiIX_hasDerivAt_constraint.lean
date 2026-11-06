-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_constraint
-- name    : BianchiIX.hasDerivAt_constraint
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:02:54.445325+00:00
-- url     : https://prove2.me/theorems/4f5cab59-e35b-4abb-9a77-925cca848a00
-- title:
--   Conservation of the Bianchi IX constraint
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
--   Let $p,s,a,b,c$ be real functions whose derivatives at a time $t$ are the five
--   components of this vector field, evaluated at $(p(t),s(t),a(t),b(t),c(t))$. Then
--   $$\frac{d}{dt}C(p(t),s(t),a(t),b(t),c(t))=0.$$
--   This identity expresses preservation of the constraint along the normalized equations.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flow.lean#L44-L57

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

theorem BianchiIX.hasDerivAt_constraint
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t) :
    HasDerivAt (fun u => constraint (p u) (s u) (a u) (b u) (c u)) 0 t := by sorry
