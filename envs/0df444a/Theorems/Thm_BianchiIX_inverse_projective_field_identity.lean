-- Prove2me | Theorems.Thm_BianchiIX_inverse_projective_field_identity
-- name    : BianchiIX.inverse_projective_field_identity
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:24:27.409544+00:00
-- url     : https://prove2.me/theorems/741fb796-3eed-427e-9e91-ca9cc48dca2f
-- title:
--   The algebraic inverse transformation of the vector field
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
--   Let $AD(y)=6$ and put
--   $B=A\kappa(y)+A^2K(u,v,w)/3$. Then
--   $$A\left(B,\frac{Bm+AF_m}{\sqrt3},\frac{Bu+AF_u}{\sqrt3},
--   \frac{Bv+AF_v}{\sqrt3},\frac{Bw+AF_w}{\sqrt3}\right)=N(\Xi_A(y)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ProjectiveInverse.lean#L33-L54

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
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

theorem BianchiIX.inverse_projective_field_identity (A m u v w : ℝ)
    (hD : A * projectiveDenom m u v w = 6) :
    let B := A * coupling u v w + A ^ 2 * curvature u v w / 3
    A • ![B, (B * m + A * phaseVelocity m u v w) / Real.sqrt 3,
      (B * u + A * strongVelocity m u v w) / Real.sqrt 3,
      (B * v + A * activeVelocity m u v w) / Real.sqrt 3,
      (B * w + A * weakVelocity m u v w) / Real.sqrt 3] =
      normalizedField ![A - 1, A * m / Real.sqrt 3, A * u / Real.sqrt 3,
        A * v / Real.sqrt 3, A * w / Real.sqrt 3] := by sorry
