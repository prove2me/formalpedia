-- Prove2me | Theorems.Thm_BianchiIX_scaled_entrance_weighted_envelope_integrals
-- name    : BianchiIX.scaled_entrance_weighted_envelope_integrals
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T16:25:57.45719+00:00
-- url     : https://prove2.me/theorems/b1f479b3-bbfb-4245-8fd1-18fd0d4e4b28
-- title:
--   Two weighted wall-envelope integrals
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
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   Define
--   $$\mathcal E_k=\{(m,u,v,w):m\geq1,\ |r(m,v)-k|\leq k/100,
--   \ 0\leq u,w\leq1/10000,\ 0\leq v\leq1\},$$
--   and $\omega_+(m,u,v,w)=s(m,u,v,w)$.
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   On the invariant plane with zero active wall, use $y=(m,u,w)\in\mathbb R^3$,
--   the inclusion $\iota(m,u,w)=(m,u,0,w)$ and the restriction
--   $\pi_s(m,u,v,w)=(m,u,w)$. Define
--   $$f(y)=\left(mu^2-(m+1)uw+w^2,
--   \frac{1-m^2-w^2+u^2}{2}u,-(m+1+uw-u^2)w\right),$$
--   $$\Delta(y)=3+m^2+(u-w)^2,\qquad f_o(y)=6f(y)/\Delta(y).$$
--   Write $J=df$, $H=d^2f$, $J_o=df_o$, $H_o=d^2f_o$ for their explicit
--   Jacobian and Hessian expressions. The denominator derivatives are
--   $d\Delta=(2m,2(u-w),2(w-u))$ and
--   $d^2\Delta(v,z)=2v_0z_0+2(v_1-v_2)(z_1-z_2)$.
--   The exact original-time boundary flow and its projected variation are
--   $$\Phi(y,t)=\pi_s\Psi_0(\iota y,t),\qquad
--   L(y,t)=\pi_s\mathcal J_{\iota y,0}(t)\iota.$$
--   For a fixed scale $K$, set $\Phi_K(y,s)=\Phi(y,Ks)$,
--   $L_K(y,s)=L(y,Ks)$ and $Q_K(y,s)=d_yL_K(y,s)$.
--   For directions $v,z$, define
--   $$S_K(y,s;v,z)=K\left[H_o(\Phi_K)(L_Kv,L_Kz)+J_o(\Phi_K)Q_K(v,z)\right].$$
--   All vector norms are sup norms, and operator norms are induced by them.
--   Write $b(y)=|u|+|w|$, $E(y)=e^{512b(y)}$, $v_s=(v_1,v_2)$, and
--   $$\mathcal H(y;v,z)=b(y)\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|,$$
--   $$B_2(y)=192b(y)(40000E(y)^3)+10000E(y)^2.$$
--   The closed boundary region is
--   $\mathcal S_c=\{(m,u,0,w):|m-c|\leq1/10,\ |u|,|w|\leq1/100\}$.
--   The boundary projection $P(m,u,w)$ is the limit of $\Phi(m,u,w;t)_0$
--   as $t\to\infty$, using the total limit convention of the formal definitions.
--
--   For $y=(m,u,v,w)$, define $p(y)=P(m,u,w)$,
--   $\rho(y)=\sqrt{(p(y)-1)^2+v^2}$, $\omega(y)=m-1-u(v+w-u)$,
--   and $\chi(y)=(\rho(y),u,v,w)$. Write $p_i=\partial_i p$.
--   The inverse differential $J_\chi(y)$ preserves the last three coordinates
--   and has first row
--   $$\left(\frac{\rho}{(p-1)p_0},-\frac{p_1}{p_0},
--   -\frac{v}{(p-1)p_0},-\frac{p_3}{p_0}\right).$$
--   An admissible local inverse $\psi$ at $y$ is $C^2$ at $\chi(y)$,
--   maps $\chi(y)$ to $y$, has derivative $J_\chi(y)$ there, and is a
--   two-sided inverse to $\chi$ on neighborhoods of these points.
--   For a scalar function $f$, write $\bar\partial_i f=d(f\circ\psi)_{\chi(y)}e_i$.
--   The radial coefficients and drift are
--   $$N(y)=m-1-u(w-u)-(p-1)p_0,\qquad B(y)=\frac{N(y)}{\rho\omega},$$
--   $$A(y)=\frac{(p-1)((1-m)p_0+w(p_1-p_3))-v^2
--   -\tfrac12(p-1)vp_1}{\rho\omega},\qquad G(y)=uvA(y)+v^2B(y).$$
--   Set
--   $$S(y)=(p-1)((p-m)-(m-1)(p_0-1))+(p-1)w(p_1-p_3)
--   -\tfrac12(p-1)vp_1,\quad H(y)=p-1-(m-1)p_0,$$
--   $$N_2(y)=(1-L^{-2})u^2+(-1+4L^{-2})uw-w^2/L^2,\qquad L=m+1,$$
--   $$R_e(y)=R_q(m,u,w),\quad
--   N_4(y)=-R_e-(m-1)\partial_0R_e-(p-m)(p_0-1),\quad
--   E(y)=\rho(y)-r(m,v).$$
--   Here
--   $$R_q(m,u,w)=P(m,u,w)-
--   \left[m+\frac{mu^2}{m^2-1}-\frac{2uw}{m+1}+\frac{w^2}{2(m+1)}\right].$$
--   The logarithmic wall rates are
--   $$a_s=\frac{1-m^2-(v-w)^2+u^2}{2\omega},\qquad
--   a_w=-1-\frac{2(1+u(v+w-u))}{\omega}.$$
--   Let $D_\chi f=df\,J_\chi$, define
--   $$c(y)=(D_\chi G\,e_0,uD_\chi G\,e_1,wD_\chi G\,e_3),$$
--   $$\mathcal A_k(y)=
--   \begin{pmatrix}uD_\chi a_s\,e_1&(w/k^2)D_\chi a_s\,e_3\\
--   k^2uD_\chi a_w\,e_1&wD_\chi a_w\,e_3\end{pmatrix},$$
--   and $\ell_k(y)=(\log u,k^2\log w)$.
--   All vector and operator norms use the sup norm.
--
--   Let $k\geq7/4$, $s\leq t$ and $Y'=aF(Y)$ on $[s,t]$,
--   where $a$ is continuous and nonnegative. Assume $Y(r)\in\mathcal E_k$
--   and $Y(r)_2>0$ throughout. Put
--   $$q(r)=a(r)\omega(Y(r)),\quad l(r)=\log Y(r)_2-\log Y(s)_2,\quad
--   (u_0,v_0,w_0)=(Y(s)_1,Y(s)_2,Y(s)_3).$$
--   Writing $(m,u,v,w)=Y(r)$ in the integrands,
--   $$\int_s^t[u+ku(v+u+w)]q\,dr\leq12u_0,$$
--   $$\int_s^t[w/k^2+uw/k+w(u+w)/k^3]q\,dr\leq6w_0/k^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/EntranceWeightedEnvelopeIntegrals.lean#L9-L84

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.scaled_entrance_weighted_envelope_integrals {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∫ r in s..t, (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) *
      (a r * entranceClockRate (Y r))) ≤ 12 * Y s 1 ∧
    (∫ r in s..t, (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3) *
      (a r * entranceClockRate (Y r))) ≤ 6 * Y s 3 / k ^ 2 := by sorry
