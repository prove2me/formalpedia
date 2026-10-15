-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_In_pdchr_1_1_2_2
-- name    : ExactVacuumAtlas.Kerr.In.pdchr_1_1_2_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:16:05.743986+00:00
-- url     : https://prove2.me/theorems/c33fead8-2be5-4de4-b322-dbbaa97a0c3b
-- title:
--   Ingoing Kerr: closed form of $\partial_r\Gamma^{r}_{\theta\theta}$
-- statement:
--   Let $M,a$ be real numbers and $x=(v,r,\theta,\varphi)$ with $\Sigma\neq0$, $\sin\theta\neq0$ ($\Sigma=r^2+a^2\cos^2\theta$). For the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed), write $U=1/\Sigma$ and let $\Gamma^a_{bc}$ be the coordinate Christoffel symbols of $(g^{\rm in},\hat g^{\rm in})$ (indices $1=r$, $2=\theta$). Then the radial slice derivative of $\Gamma^{1}_{22}$ at $x$ equals $$\partial_r\Gamma^{r}_{\theta\theta}(x)=-4Mr^3U^2+4MrU+2a^2r^2U^2-a^2U+2r^4U^2-3r^2U.$$ The **coordinate Ricci tensor** is the one of the definition bundle `Atlas_Core_Basic`: with $\partial_i f(x)$ the derivative of the slice $u\mapsto f(x[x_i:=u])$ at $u=x_i$, $$\Gamma^a_{bc}=\tfrac12\sum_k \hat g^{ak}\big(\partial_c g_{kb}+\partial_b g_{kc}-\partial_k g_{bc}\big),\qquad R_{bd}=\sum_i\Big(\partial_i\Gamma^i_{bd}-\partial_d\Gamma^i_{bi}+\sum_j\big(\Gamma^i_{ij}\Gamma^j_{bd}-\Gamma^i_{dj}\Gamma^j_{bi}\big)\Big).$$ Here $\hat g$ is the candidate inverse supplied with the metric; whether it is a genuine inverse is a separate obligation.
--
--   A generated closed-form entry of the ingoing-Kerr derivative table, promoted to its own node because it is shared by the component lemma $R_{22}$ and the table; it is a rational identity in $r,\sin\theta,\cos\theta,1/\Sigma$.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/InTables.lean#L1233-L1239 (module Atlas.Kerr.InTables, file sha256 7c404b4484bf8d2f09a4714c57b6ab6bbdd8e3352fb7deab29457264bccdbc6e; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_In_pdchr_1_1_2_2.lean)

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

theorem ExactVacuumAtlas.Kerr.In.pdchr_1_1_2_2 (x : Pt 4) (hx : x ∈ domIn a) :
    pd 1 (christoffel (gIn M a) (giIn M a) 1 2 2) x = ((-4:ℝ) * M) * (x 1) ^ 3 * Ui a (x 1) (x 2) ^ 2 + ((4:ℝ) * M) * (x 1) * Ui a (x 1) (x 2) + ((2:ℝ) * a^2) * (x 1) ^ 2 * Ui a (x 1) (x 2) ^ 2 + ((-1:ℝ) * a^2) * Ui a (x 1) (x 2) + ((2:ℝ)) * (x 1) ^ 4 * Ui a (x 1) (x 2) ^ 2 + ((-3:ℝ)) * (x 1) ^ 2 * Ui a (x 1) (x 2) := by sorry
