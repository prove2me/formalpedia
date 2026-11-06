-- Prove2me | Theorems.Thm_BianchiIX_stableCorrectedPhase_coefficient_bounds
-- name    : BianchiIX.stableCorrectedPhase_coefficient_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T16:24:06.044426+00:00
-- url     : https://prove2.me/theorems/cf2d804f-f902-404f-81c5-3dc8727e9c49
-- title:
--   Amplitude and radial scales of the corrected phase coefficients
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
--   Set $r=\sqrt{(m+1)^2+w^2}$ and
--   $$A(m)=\frac{m}{m^2-1},\quad C(m)=-\frac2{m+1},\quad
--   \Theta(m,u,w)=r-1+A(m)u^2+C(m)uw.$$
--   Its explicit gradient is used together with the residual
--   $R=r_4u^4+r_3u^3w+r_2u^2w^2+r_1uw^3$, where
--   $$r_4=-\frac{2m}{(m^2-1)^2},\quad r_3=\frac{2(3m-1)}{(m^2-1)^2},$$
--   $$r_2=-\frac{m^2+1}{(m^2-1)^2}-\frac m{m^2-1}
--   +\frac{r+1}{r(r+m+1)},\quad
--   r_1=\frac2{(m+1)^2}+\frac1{m+1}-\frac1{r+m+1}.$$
--
--   Write $L=m+1$, $b=|u|+|w|$, $v_s=(v_1,v_2)$, and set
--   $$W_b(v)=b\|v\|+\|v_s\|,\quad
--   H_s(y;v,z)=|u|\|v\|\|z\|+|v_0||z_1|+|v_1||z_0|
--   +b(|v_1|\|z\|+\|v\||z_1|).$$
--   The corrected and quadratic remainders are
--   $$R_c=P-\Theta,\quad R_q=P-\left(m+A(m)u^2+C(m)uw+\frac{w^2}{2L}\right).$$
--   For $K\in\mathbb R$, let $a_i(K,y)=6K r_{4-i}(m,w)/\Delta(y)$,
--   where $r_4,r_3$ are independent of $w$, and put
--   $$M(y)=(u^3,u^2w,uw^2,w^3),\quad C_K(y)=\sum_{i=0}^3a_i(K,y)M_i(y),$$
--   $$g_{K,s}(y)=\frac{6K}{\Delta(\Phi_K(y,s))}R(\Phi_K(y,s)).$$
--   The cubic derivative budgets are
--   $$B_1(y;v)=b^3\|v\|+3b^2\|v_s\|,$$
--   $$B_2^c(y;v,z)=b^3\|v\|\|z\|
--   +3b^2(\|v\|\|z_s\|+\|v_s\|\|z\|)+6b\|v_s\|\|z_s\|.$$
--   A direction is radial if its last two coordinates vanish, and transverse
--   if its zeroth coordinate vanishes.
--   For $m\geq2$ and arbitrary signed $u,w$,
--   $$|\Theta_m-1|\leq8b^2/L^2,\quad|\Theta_u|\leq6b/L,\quad|\Theta_w|\leq3b/L,$$
--   $$|\Theta_{mm}|\leq33b^2/L^3,\quad
--   |\Theta_{mu}|\leq12b/L^2,\quad|\Theta_{mw}|\leq3b/L^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/StablePhaseJetBounds.lean#L7-L72

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

theorem BianchiIX.stableCorrectedPhase_coefficient_bounds {m u w : ℝ} (hm : 2 ≤ m) :
    let b := |u| + |w|
    |stableCorrectedGradient m u w 0 - 1| ≤ 8 / (m + 1) ^ 2 * b ^ 2 ∧
      |stableCorrectedGradient m u w 1| ≤ 6 / (m + 1) * b ∧
      |stableCorrectedGradient m u w 2| ≤ 3 / (m + 1) * b ∧
      |w ^ 2 / stableWeakRadius m w ^ 3 + stableCorrectionASecond m * u ^ 2 +
        stableCorrectionCSecond m * u * w| ≤ 33 / (m + 1) ^ 3 * b ^ 2 ∧
      |2 * stableCorrectionADeriv m * u + stableCorrectionCDeriv m * w| ≤ 12 / (m + 1) ^ 2 * b ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3 + stableCorrectionCDeriv m * u| ≤ 3 / (m + 1) ^ 2 * b := by sorry
