-- Prove2me | Theorems.Thm_BianchiIX_exists_era_joint_statistics
-- name    : BianchiIX.exists_era_joint_statistics
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:47:22.115193+00:00
-- url     : https://prove2.me/theorems/1a3354e3-73bc-4d1d-b484-4ec1211a133f
-- title:
--   A common Borel statistical domain for all admissible era curves
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
--   For real $k$, put $\varepsilon_k=1/(10000k)$ and define
--   $$\mathcal K_k=\{(m,u,v,w): |E(m,v)-k^2|\leq1/8,\quad v\geq1,
--   \quad0\leq u\leq\varepsilon_k,\quad0\leq vw\leq\varepsilon_k\}.$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Write $G(y)=6F(y)/D(y)$, $\lambda(y)=6r_yd_y/D(y)$, and
--   $S_k(R,U,P)=(R,kU,P)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),
--   \qquad \mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}(\mathcal J_{y,t_0}(t)w).$$
--   The entrance parametrization and radial exit factor are
--   $$e(k,u,w)=(1+\sqrt{k^2-1},u,1,w),$$
--   $$f_y=\mathcal V(\theta_y,\eta(y))_0,\qquad c_y=-\tanh\theta_y,
--   \qquad h_y=c_y+f_y/r_y,\qquad \rho_y=c_y/h_y.$$
--   For projective initial data $y$, put
--   $$A_{y,t_0}(t)=1+(\alpha_{\Xi(y),t_0}(t))_0.$$
--   Coordinates of three-vectors are indexed by $0,1,2$; projective
--   coordinates are indexed by $m,u,v,w$.
--
--   For $Y\in\mathbb R^3$, put $x_Y=\Xi(e(Y))$,
--   $\beta_Y(t)=\Psi_0(e(Y),t)$, and
--   $$H_Y=\{t>0:t\in I_{\max}(x_Y,0),\ (\beta_Y(t))_v=1\},
--   \qquad T(Y)=\inf H_Y,\qquad F(Y)=\eta(\beta_Y(T(Y))).$$
--   The infimum uses the total real-order convention. Write $\operatorname{Valid}(Y)$
--   when $T(Y)$ is the least element of $H_Y$, every $t\in[0,T(Y)]$ lies in
--   $I_{\max}(x_Y,0)$ with $A_{e(Y),0}(t)>0$, the active wall is strictly
--   above one for $0<t<T(Y)$, and
--   $$dg_{\alpha_{x_Y,0}(T(Y))}N(\alpha_{x_Y,0}(T(Y)))<0,
--   \qquad g(x)=(\Pi(x))_v.$$
--   All vector and operator norms below use the finite-product supremum norm.
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
--   $$\mathcal C_\mu=\{(m,u,v,w):|-m-\mu|\leq1/2,
--   \ 0\leq u\leq1/10000,\ 0\leq v,w\leq1\},$$
--   $$\omega_-(y)=s(-y_m,y_u,y_v,y_w),\qquad H(y)=F(y)/\omega_-(y).$$
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
--
--   For $p=(\mu,u,w)\in\mathbb R^3$, set $e(p)=(-\mu,u,1,w)$,
--   $x_p=\Xi(e(p))$, and
--   $$T_-(p)=\inf\{t>0:t\in I_{\max}(x_p,0),\ (\Psi_0(e(p),t))_w=1\},
--   \qquad P_-(p)=\Psi_0(e(p),T_-(p)).$$
--   Let $V_-(p)$ mean that this infimum is a least element, the full interval
--   $[0,T_-(p)]$ lies in the maximal domain with positive $A$, the growing wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive at the endpoint. The infimum has its total real-order meaning.
--
--   Write $e_+(R,u,w)=(1+\sqrt{R^2-1},u,1,w)$,
--   $e_-(R,u,w)=(1-\sqrt{R^2-1},u,1,w)$,
--   $p_-(R,u,w)=(\sqrt{R^2-1}-1,u,w)$, and
--   $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
--   The physical connection coordinates are
--   $$\mathscr C(p)=\left(\sqrt{(-P_-(p)_0-1)^2+1},P_-(p)_1,P_-(p)_2\right).$$
--   Below $T$ denotes the canonical core return time from $e_+$ and
--   $F(Y)=\eta(\Psi_0(e_+(Y),T(Y)))$ its radial and wall coordinates.
--   Let $\mathscr R(Y)=\mathscr C(p_-(Y))$, $t_r(Y)=T_-(p_-(Y))$,
--   $G=\mathscr R\circ F$, and $t_G(Y)=T(Y)+t_r(F(Y))$.
--   A cone direction at $Y$ has $d_0=1$,
--   $|d_1|\leq\sqrt{Y_1}$, $|d_2|\leq\sqrt{Y_2}$.
--   For a map $H$ with positive output walls, its positive cone property means
--   $dH(Y)d$ has positive radial component and
--   $|(dH(Y)d)_i|\leq\sqrt{H(Y)_i}(dH(Y)d)_0$ for $i=1,2$.
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
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
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
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   In the era formulas below, $F$ denotes the core return map and
--   $G=\mathscr R\circ F$ its composition with reflection.
--   For $Z=(R,u,w)$ use the natural height $h_*(Z)=\eta((R-2)/2)^J$ and define
--   $S_*(Z)=\mathcal P(h_*(Z),Z)$,
--   $R_*(Z)=r(S_*(Z)_0,S_*(Z)_2)$,
--   $Q_*(Z)=2/R_*(Z)$ and $t_*(Z)=\mathcal T(h_*(Z),Z)$.
--   The complete era maps are
--   $$Z_m=F\circ G^m,\qquad S_m=S_*\circ Z_m,\qquad
--   R_m=R_*\circ Z_m,\qquad P_m=2/R_m.$$
--   For a graph $\Gamma=(U,W)$ write $\Gamma[r]=(r,U(r),W(r))$,
--   $\phi_m(r)=P_m(\Gamma[r])$, $k_m(r)=R_m(\Gamma[r])$,
--   $u_m(r)=S_m(\Gamma[r])_1$, $w_m(r)=S_m(\Gamma[r])_3$.
--   Let $\operatorname{Inv}_{a,b}(f)$ denote Lean's total choice inverse
--   $\operatorname{invFunOn}f\,[a,b]$. For
--   $a=2(m+1+\beta)$, $b=2(m+2-\beta)$, define
--   $$g_m=\operatorname{Inv}_{a,b}(\phi_m),\qquad h_m(y)=2/g_m(y).$$
--   Write $\gamma_n(y)=1/(n+y)$ for the Gauss inverse branch.
--   The retained phase set is
--   $\mathcal H_N=\bigcup_{m<N}(h_m(1-2\beta),h_m(2\beta))$.
--
--   A curve $\Gamma=(U,W)$ is admissible at budget $B$ if, for every $r>2$,
--   $U(r),W(r)>0$, $U(r)+W(r)\leq B$, both functions are $C^1$ at $r$,
--   and $|U'(r)|\leq\sqrt{U(r)}$, $|W'(r)|\leq\sqrt{W(r)}$.
--   For an arbitrary graph, define its successor walls by
--   $$U_m^+=\mathfrak E_{k_m,u_m}^{a,b;\,2/(1-2\beta),\,1/\beta},\qquad
--   W_m^+=\mathfrak E_{k_m,w_m}^{a,b;\,2/(1-2\beta),\,1/\beta},$$
--   where $\mathfrak E$ is the canonical amplitude extension after composing with
--   the choice inverse of $k_m$, with slope $u_m'/k_m'$ or $w_m'/k_m'$.
--   The one-step property at $(\eta,J,\sigma,B,C)$ consists of the following.
--   Put $\beta=B^\sigma$, $N=\lfloor1/\beta\rfloor_{\mathbb N}$,
--   $K_\beta=[2\beta,1-2\beta]$. One has $0<\beta<1/160$. For every $m<N$,
--   $h_m$ is strictly decreasing on $K_\beta$, and for $y\in K_\beta$,
--   $$\frac1{m+2}<h_m(y)<\frac1{m+1},\quad \phi_m(2/h_m(y))=y,
--   \quad h_m\text{ is }C^1\text{ at }y,\quad h_m'(y)<0,$$
--   $$|h_m(y)-\gamma_{m+1}(y)|\leq CB/(m+1)^2,\quad
--   \left|\log\frac{|h_m'(y)|}{|\gamma_{m+1}'(y)|}\right|\leq5C\sqrt B.$$
--   The successor $(U_m^+,W_m^+)$ is admissible at budget $B^{4/3}$ and,
--   with $r=2/h_m(y)$, satisfies
--   $k_m(r)=2/y$, $U_m^+(2/y)=u_m(r)$, $W_m^+(2/y)=w_m(r)$.
--   The retained branch intervals are pairwise disjoint and
--   $\lambda((0,1)\setminus\mathcal H_N)\leq10B^\sigma$.
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--
--   For a state $(B,X)$ let
--   $\mathcal F_m(B,X)=(B^{4/3},(R_m(X),S_m(X)_1,S_m(X)_3))$.
--   Its selected domain $D_m(B_{\rm cap})$ is defined by
--   $$0<B\leq B_{\rm cap},\quad m<\lfloor B^{-\sigma}\rfloor_{\mathbb N},
--   \quad X_1,X_2>0,\quad X_1+X_2\leq B,$$
--   $$2(m+1+B^\sigma)\leq X_0\leq2(m+2-B^\sigma),\quad
--   2B^\sigma<P_m(X)<1-2B^\sigma.$$
--   For positive-digit words define $D_\varnothing$ to be the whole state space and
--   $D_{a w}=D_{a-1}(B_{\rm cap})\cap\mathcal F_{a-1}^{-1}D_w$.
--   The survivor domain is $D_\infty=\bigcap_n\bigcup_{|w|=n}D_w$.
--   For $p\in D_\infty$, choose its compatible words $w_n$ and digits
--   $a_n$ with $w_{n+1}=w_n a_n$. Let
--   $y_n(p)=2/(\mathcal F_{w_n}(p))_{X,0}$ and let $\pi(a)$ be the
--   continued-fraction code. The common typical domain is
--   $$\mathcal D=\{p\in D_\infty:\pi(a(p))\in\mathcal B_G\},$$
--   where $\mathcal B_G$ is the set of points with all Gauss cylinder frequencies.
--   For a curve of budget $B$, set
--   $\mathcal T_\Gamma=\{x\in(0,1):(B,\Gamma[2/x])\in\mathcal D\}$.
--   The curve family begins at $\Gamma$ and uses its successor for retained
--   digits; other descendants use the constant pair $(M_{n+1}(B)/2,M_{n+1}(B)/2)$.
--   At a word of length $n$, its inverse branch for digit $a$ is $h_{a-1}$,
--   with $\beta=M_n(B)^\sigma$, on $(2\beta,1-2\beta)$ if
--   $a-1<\lfloor1/\beta\rfloor_{\mathbb N}$, and has empty domain otherwise.
--   These branches and supplied one-step properties define an inverse tree.
--   Its realization states that each branch edge agrees with $\mathcal F_{a-1}$
--   and that its image is exactly the selected domain on that curve.
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $G(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $G(0)=0$.
--   For a finite word $w=(a_0,\ldots,a_{k-1})$ of natural numbers, set
--   $$C_w=(g_{a_0}\circ\cdots\circ g_{a_{k-1}})((0,1)),\qquad
--   g_a(t)=1/(a+t),$$
--   where the empty composition is the identity and $0^{-1}=0$. Define
--   $$f_w=\mathbf1_{C_w},\qquad m_w=\mu_G(C_w),\qquad
--   \mathcal B_G=\left\{x\in\mathbb R:\ \forall w,\
--   \frac1n\sum_{j=0}^{n-1}f_w(G^jx)\longrightarrow m_w\right\}.$$
--   For a positive-digit sequence $a$, write $\pi(a)$ for its continued-fraction
--   code, $\sigma^j a$ for its tail beginning at $j$, and $a|_k$ for its first
--   $k$ digits.
--
--   Define the natural-valued digit, tail observables, and truncations by
--   $$D(x)=\lfloor1/x\rfloor_{\mathbb N},\qquad
--   H_k(x)=\mathbf1_{(0,1/k)}(x)\quad(k\geq1),\qquad
--   D_R(x)=\min(D(x),R)\quad(R\in\mathbb N).$$
--   Here the natural floor is zero for negative arguments, and $0^{-1}=0$.
--   Write
--   $$p_k=\frac{\log((k+1)^2/(k(k+2)))}{\log2},\qquad
--   q_k=\frac{\log(1+1/k)}{\log2},\qquad
--   t_R=\frac{\log(R+1)}{\log2}.$$
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   For a positive-digit sequence $a$ and a real sequence $y$, let
--   $\mathcal E(a,y)$ mean all of the following statements:
--   $$A_N(f\circ y)\to\int f\,d\mu_G
--   \quad\text{for every }f:\mathbb R\to\mathbb R
--   \text{ continuous on }[0,1],$$
--   $$A_N(j\mapsto\mathbf1_{\{(\sigma^ja)|_{|w|}=w\}})\to m_w
--   \quad\text{for every finite positive-digit word }w,$$
--   $$A_N(j\mapsto\mathbf1_{\{a_j=k\}})\to p_k,\qquad
--   A_N(j\mapsto\mathbf1_{\{k\leq a_j\}})\to q_k\quad(k\geq1),$$
--   $$A_N(j\mapsto\min(a_j,R))\to t_R\quad(R\in\mathbb N),\qquad
--   A_N(j\mapsto a_j)\to+\infty.$$
--   For a measurable space $X$, let $(\mathrm B)_X$ be
--   the following proposition: for every probability measure $\mu$ on $X$,
--   every ergodic map $F:X\to X$, and every integrable $f:X\to\mathbb R$,
--   $$\frac1n\sum_{j=0}^{n-1}f(F^jx)\longrightarrow\int_X f\,d\mu
--   \quad\text{for }\mu\text{-almost every }x.$$
--   This proposition is an explicit hypothesis in the results that use it.
--
--   Assume $(\mathrm B)_{\mathbb R}$. There is $0<\delta\leq1/40000$ such
--   that for $0<\eta\leq\delta$, $J\geq20$, $0<\sigma<1$, $2J\sigma<1$,
--   there exists $0<B_{\rm cap}<1$ for which the common typical domain
--   $\mathcal D$ is Borel measurable. There is also $0<B_*\leq B_{\rm cap}$
--   such that for every $0<B\leq B_*$ and every admissible curve $\Gamma$
--   of budget $B$, the set $\mathcal T_\Gamma$ is measurable,
--   $\lambda(\mathcal T_\Gamma)>1/2$, and for every set $I\subset\mathbb R$,
--   $$\lambda\bigl((I\cap(0,1))\setminus(I\cap\mathcal T_\Gamma)\bigr)
--   \leq\min\{\lambda(I),80B^\sigma\}.$$
--   For every $x\in\mathcal T_\Gamma$ there is a survivor
--   $p=(B,\Gamma[2/x])$ whose digits and phases satisfy
--   $\mathcal E(a(p),y(p))$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraJointStatistics.lean#L10-L65

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Definitions.Def_BianchiIX_EraCodingData
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.exists_era_joint_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ MeasurableSet (EraSurvivor.typicalDomain η J σ Bcap) ∧
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
            ∀ Γ : EraCurve, Γ.Admissible B →
              MeasurableSet (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (1 / 2 : ℝ≥0∞) < volume (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (∀ I : Set ℝ, volume ((I ∩ Ioo 0 1) \ (I ∩ EraSurvivor.curveTypicalSet Γ η J σ B Bcap)) ≤
                min (volume I) (ENNReal.ofReal (80 * B ^ σ))) ∧
              ∀ x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap,
                ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Γ.state (2 / x)) ∧
                  EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by sorry
