-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_In_ricci_3_0
-- name    : ExactVacuumAtlas.Kerr.In.ricci_3_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:17:48.086988+00:00
-- url     : https://prove2.me/theorems/e230953c-9261-4d1a-a9eb-6bb20454d04d
-- title:
--   Ingoing Kerr: Ricci component $R_{30}$ vanishes on the ingoing domain
-- statement:
--   Let $M,a$ be arbitrary real numbers and let $x=(v,r,\theta,\varphi)\in\mathbb R^4$ satisfy $\Sigma\neq0$ and $\sin\theta\neq0$, where $\Sigma=r^2+a^2\cos^2\theta$. Consider the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed). Then the $(3,0)$ component of the coordinate Ricci tensor of $(g^{\rm in},\hat g^{\rm in})$ vanishes at $x$: $$R_{30}(x)=0.$$ The **coordinate Ricci tensor** is the one of the definition bundle `Atlas_Core_Basic`: with $\partial_i f(x)$ the derivative of the slice $u\mapsto f(x[x_i:=u])$ at $u=x_i$, $$\Gamma^a_{bc}=\tfrac12\sum_k \hat g^{ak}\big(\partial_c g_{kb}+\partial_b g_{kc}-\partial_k g_{bc}\big),\qquad R_{bd}=\sum_i\Big(\partial_i\Gamma^i_{bd}-\partial_d\Gamma^i_{bi}+\sum_j\big(\Gamma^i_{ij}\Gamma^j_{bd}-\Gamma^i_{dj}\Gamma^j_{bi}\big)\Big).$$ Here $\hat g$ is the candidate inverse supplied with the metric; whether it is a genuine inverse is a separate obligation.
--
--   One of the sixteen component lemmas assembled into the ingoing-Kerr vacuum certificate (`ExactVacuumAtlas.Kerr.In.cert`); each component is proved separately because $R_{bd}$ is not assumed symmetric. The domain is $U^{\rm in}_a=\{x:\ \Sigma\neq0,\ \sin\theta\neq0\}$. There is no $\Delta\neq0$ restriction, so the statement also applies at points with $\Delta=0$, precisely where $\Sigma\neq0$ and $\sin\theta\neq0$ hold as well. Whether such points exist depends on $(M,a)$: `ExactVacuumAtlas.Release01.coverage` exhibits one in the sufficient parameter regime $M>0$, $a^2\le M^2$. No horizon statement is made.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/InTables.lean#L2300-L2312 (module Atlas.Kerr.InTables, file sha256 7c404b4484bf8d2f09a4714c57b6ab6bbdd8e3352fb7deab29457264bccdbc6e; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_In_ricci_3_0.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
open Real
open ExactVacuumAtlas
open ExactVacuumAtlas
open ExactVacuumAtlas.Kerr
open ExactVacuumAtlas.Kerr.In
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M a : ℝ)

theorem ExactVacuumAtlas.Kerr.In.ricci_3_0 (x : Pt 4) (hx : x ∈ domIn a) :
    ricciOf (gIn M a) (giIn M a) 3 0 x = 0 := by sorry
