-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_EF_ricci_0_0
-- name    : ExactVacuumAtlas.Schwarzschild.EF.ricci_0_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:36:45.53276+00:00
-- url     : https://prove2.me/theorems/23b4f7c7-3ed9-4b60-9dd3-bed0f13d46b6
-- title:
--   Eddington–Finkelstein Schwarzschild: Ricci component $R_{00}$ vanishes, including $r=2M$
-- statement:
--   Let $M,\varepsilon$ be real numbers with $\varepsilon^2=1$ and let $x=(w,r,\theta,\varphi)$ satisfy $r>0$ and $0<\theta<\pi$. Consider the **Eddington–Finkelstein family** $g^{\rm EF}_{M,\varepsilon}$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(w,r,\theta,\varphi)$ with $w=v$ for $\varepsilon=1$ ingoing and $w=u$ for $\varepsilon=-1$ outgoing): $g_{ww}=-(1-2M/r)$, $g_{wr}=g_{rw}=\varepsilon$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{wr}=\hat g^{rw}=\varepsilon$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, other entries $0$. Then the $(0,0)$ component of the coordinate Ricci tensor of $(g^{\rm EF}_{M,\varepsilon},\hat g^{\rm EF}_{M,\varepsilon})$ vanishes at $x$: $$R_{00}(x)=0.$$ The **coordinate Ricci tensor** is the one of the definition bundle `Atlas_Core_Basic`: with $\partial_i f(x)$ the derivative of the slice $u\mapsto f(x[x_i:=u])$ at $u=x_i$, $$\Gamma^a_{bc}=\tfrac12\sum_k \hat g^{ak}\big(\partial_c g_{kb}+\partial_b g_{kc}-\partial_k g_{bc}\big),\qquad R_{bd}=\sum_i\Big(\partial_i\Gamma^i_{bd}-\partial_d\Gamma^i_{bi}+\sum_j\big(\Gamma^i_{ij}\Gamma^j_{bd}-\Gamma^i_{dj}\Gamma^j_{bi}\big)\Big).$$ Here $\hat g$ is the candidate inverse supplied with the metric; whether it is a genuine inverse is a separate obligation.
--
--   One of the sixteen component lemmas assembled into the Eddington–Finkelstein certificate (`ExactVacuumAtlas.Schwarzschild.EF.cert`, both signs $\varepsilon=\pm1$ at once). The domain is $U^{\rm EF}=\{x:\ r>0,\ 0<\theta<\pi\}$ ($w,\varphi$ arbitrary). For $M>0$ it includes the regular-coordinate portion of $r=2M$ with $0<\theta<\pi$; the polar axis, angular identifications and global horizon geometry are not included.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Schwarzschild/EFTables.lean#L1570-L1576 (module Atlas.Schwarzschild.EFTables, file sha256 2d405f2fe5b944403d7d4676cca77cca487bfbbc457767770edb6657cc24131d; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_EF_ricci_0_0.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M ε : ℝ)

theorem ExactVacuumAtlas.Schwarzschild.EF.ricci_0_0 (x : Pt 4) (hx : x ∈ domEF)  (hε : ε ^ 2 = 1) :
    ricciOf (gEF M ε) (giEF M ε) 0 0 x = 0 := by sorry
