-- Prove2me | Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
-- name    : BianchiIX.coreAuxiliary_coefficient_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:06:24.308902+00:00
-- url     : https://prove2.me/theorems/6cc8ecdb-b284-4f5d-8367-7f24951b9f25
-- title:
--   Uniform bounds for the auxiliary core quantities and their derivatives
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
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   At $(z,Y)$ use the abbreviations
--   $$s=1/\cosh z,\quad c=-\tanh z,\quad \delta=u-w,$$
--   $$C=u(v+w-u),\quad a=-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r),
--   \quad g=-C+c\delta^2/r.$$
--   Let $\mathcal Q(z,Y)=(C,d,a,g)$. Define the $4\times3$ matrix $H(z,Y)$
--   by its rows, in the order $(C,d,a,g)$ and columns $(r,u,p)$:
--   $$H_C=(u(s-w/r),\ v-2u+w,\ u/v),$$
--   $$H_d=(2\delta(u-2w)/r^3,\ -2\delta/r^2,\ 2\delta/(vr^2)),$$
--   $$H_a=(-1/2-sw/r+(3w^2-u^2)/(2r^2),\ u/r,\ (1-w/v)/r),$$
--   $$H_g=(-u(s-w/r)+c\delta(3w-u)/r^2,\
--   -(v-2u+w)+2c\delta/r,\ -u/v-2c\delta/(rv)).$$
--
--   For $j=0,1,2$, define the $3\times3$ matrix $A(z,Y)$ by
--   $$A_{0j}=H_{gj}/d-gH_{dj}/d^2,$$
--   $$A_{1j}=\delta_{j1}a/d+uH_{aj}/d-uaH_{dj}/d^2,$$
--   $$A_{2j}=\delta_{j0}\frac{2p(1+C)}{r^2d}
--   -\delta_{j2}\frac{2(1+C)}{rd}-\frac{2pH_{Cj}}{rd}
--   +\frac{2p(1+C)H_{dj}}{rd^2},$$
--   where $\delta_{ij}$ is the Kronecker symbol.
--
--   For real $k$, define $S_k(\xi_0,\xi_1,\xi_2)=(\xi_0,k\xi_1,\xi_2)$ and
--   $$B_k(z,Y)=\begin{pmatrix}
--   A_{00}&A_{01}/k&A_{02}\\
--   kA_{10}&A_{11}&kA_{12}\\
--   A_{20}&A_{21}/k&A_{22}
--   \end{pmatrix}.$$
--
--   In the following coefficient estimate, assume
--   $$k\geq6,\qquad \frac{99k}{100}\leq r\leq\frac{101k}{100},
--   \qquad v=\frac r{\cosh z}\geq1,$$
--   $$0\leq u,w\leq\varepsilon_k,\qquad
--   \varepsilon_k=\frac1{10000k},\qquad w=p/v.$$
--   Write $\varepsilon=\varepsilon_k$.
--   For $\mathcal Q=(C,d,a,g)$ and its derivative matrix $H$, one has
--   $$0\leq C\leq\frac1{100},\quad |a|\leq r,\quad
--   |g|\leq2r\varepsilon,\quad d\geq\frac{999}{1000},$$
--   $$|H_{C0}|\leq u,\quad |H_{C1}|\leq2r,$$
--   $$|H_{d0}|\leq\frac\varepsilon{r^2},\quad
--   |H_{d1}|\leq\frac{2\varepsilon}{r^2},\quad
--   |H_{d2}|\leq\frac{2\varepsilon}{vr^2},$$
--   $$|H_{a0}|\leq\frac34,\quad |H_{a2}|\leq\frac1r,$$
--   $$|H_{g0}|\leq2\varepsilon,\quad |H_{g1}+v|\leq3\varepsilon,
--   \quad |H_{g2}|\leq\frac{2\varepsilon}v.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreCoefficientBounds.lean#L8-L64

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open BianchiIX

theorem BianchiIX.coreAuxiliary_coefficient_bounds {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let r := y 0
    let v := r / Real.cosh z
    let m := (1 / 10000) / k
    let q := coreAuxiliary z y
    let h := coreAuxiliaryJacobian z y
    (0 ≤ q 0 ∧ q 0 ≤ 1 / 100) ∧ |q 2| ≤ r ∧ |q 3| ≤ 2 * r * m ∧
    999 / 1000 ≤ q 1 ∧
    |h 0 0| ≤ y 1 ∧ |h 0 1| ≤ 2 * r ∧
    |h 1 0| ≤ m / r ^ 2 ∧ |h 1 1| ≤ 2 * m / r ^ 2 ∧ |h 1 2| ≤ 2 * m / (v * r ^ 2) ∧
    |h 2 0| ≤ 3 / 4 ∧ |h 2 2| ≤ 1 / r ∧
    |h 3 0| ≤ 2 * m ∧ |h 3 1 + v| ≤ 3 * m ∧ |h 3 2| ≤ 2 * m / v := by sorry
