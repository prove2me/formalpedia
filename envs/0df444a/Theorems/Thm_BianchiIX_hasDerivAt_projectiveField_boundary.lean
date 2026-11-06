-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_projectiveField_boundary
-- name    : BianchiIX.hasDerivAt_projectiveField_boundary
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:47:53.107538+00:00
-- url     : https://prove2.me/theorems/b122652e-2dc8-48c2-91b0-ca833bcd7759
-- title:
--   Differentiating the projective field at a boundary state
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   For $\xi=(\xi_m,\xi_u,\xi_v,\xi_w)$, define
--   $$\mathcal L_{m,v}\xi=
--   \left((1-m)v\xi_u-2v\xi_v,\ \frac{1-m^2-v^2}{2}\xi_u,
--   v\xi_m-v^2\xi_u+(m-1)\xi_v,\ (-m-1)\xi_w\right).$$
--   If $\gamma'(t)=\xi$ and
--   $\gamma(t)=(m,0,v,0)$, then
--   $$\frac{d}{dt}F(\gamma(t))=\mathcal L_{m,v}\xi.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ProjectiveLinearization.lean#L20-L51

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX

theorem BianchiIX.hasDerivAt_projectiveField_boundary {gamma : ℝ → ProjectiveState}
    {xi : ProjectiveState} {t m v : ℝ}
    (hg : HasDerivAt gamma xi t) (hb : gamma t = ![m, 0, v, 0]) :
    HasDerivAt (fun s => projectiveField (gamma s)) (projectiveBoundaryVariation m v xi) t := by sorry
