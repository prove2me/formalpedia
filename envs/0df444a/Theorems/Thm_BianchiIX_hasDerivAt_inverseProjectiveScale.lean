-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_inverseProjectiveScale
-- name    : BianchiIX.hasDerivAt_inverseProjectiveScale
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:28:24.602793+00:00
-- url     : https://prove2.me/theorems/f394f589-d13e-4b2c-9d1b-fb86d9703e7c
-- title:
--   Evolution of the inverse projective scale
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
--   If $\beta'(\tau)=F(\beta(\tau))$ and
--   $D(\beta(\tau))\ne0$, put $y=\beta(\tau)$ and $A=6/D(y)$. Then
--   $$\frac{d}{d\tau}\frac6{D(\beta(\tau))}
--   =A\kappa(y)+\frac{A^2}{3}K(u,v,w).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ProjectiveInverse.lean#L23-L31

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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

theorem BianchiIX.hasDerivAt_inverseProjectiveScale {β : ℝ → ProjectiveState} {τ : ℝ}
    (hβ : HasDerivAt β (projectiveField (β τ)) τ)
    (hD : projectiveStateDenom (β τ) ≠ 0) :
    HasDerivAt (fun t => 6 / projectiveStateDenom (β t))
      ((6 / projectiveStateDenom (β τ)) * coupling (β τ 1) (β τ 2) (β τ 3) +
        (6 / projectiveStateDenom (β τ)) ^ 2 * curvature (β τ 1) (β τ 2) (β τ 3) / 3) τ := by sorry
