-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_wallAmplitude
-- name    : BianchiIX.hasDerivAt_wallAmplitude
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:40:03.456639+00:00
-- url     : https://prove2.me/theorems/a4488de5-9a32-4a4c-8e11-b6888b931491
-- title:
--   The wall amplitude satisfies an exact scalar evolution equation
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
--   Define $H(a,b,c)=(abc)^{2/3}$ and
--   $$\Delta(q,h)=\frac{2(q+4h)}{1+4h}.$$
--   Real powers and division have their total Lean meanings.
--   Let $p,s,a,b,c:\mathbb R\to\mathbb R$.
--   At a time $t$, assume $a(t),b(t),c(t)>0$ and
--   $a'=r_1a$, $b'=r_2b$, $c'=r_3c$. Then
--   $$\frac{d}{dt}H(a,b,c)=-2S(p,s)H(a,b,c).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flux.lean#L147-L161

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section

theorem BianchiIX.hasDerivAt_wallAmplitude
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t)
    (ha0 : 0 < a t) (hb0 : 0 < b t) (hc0 : 0 < c t) :
    HasDerivAt (fun x => wallAmplitude (a x) (b x) (c x))
      (-2 * shearSq (p t) (s t) * wallAmplitude (a t) (b t) (c t)) t := by sorry
