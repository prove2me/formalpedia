-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_EFRelation_pullback
-- name    : ExactVacuumAtlas.Schwarzschild.EFRelation.pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:34:36.267821+00:00
-- url     : https://prove2.me/theorems/60ca0451-e43c-47a9-a3d1-490065d63324
-- title:
--   Standard Schwarzschild metric is the pull-back of the Eddington–Finkelstein metric
-- statement:
--   Let $M,\varepsilon$ be real numbers with $\varepsilon^2=1$ and $x=(t,r,\theta,\varphi)\in U^{\rm std}_M=\{r>0,\ r\neq2M,\ 0<\theta<\pi\}$. Let $\Phi_{M,\varepsilon}(t,r,\theta,\varphi)=(t+\varepsilon(r+2M\log\lvert r-2M\rvert),r,\theta,\varphi)$ and $$J(x)=\begin{pmatrix}1&\varepsilon\big(1+\frac{2M}{r-2M}\big)&0&0\\0&1&0&0\\0&0&1&0\\0&0&0&1\end{pmatrix}.$$ Then, with $g^{\rm std}_M$ the **standard Schwarzschild metric** $g^{\rm std}_M$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-(1-2M/r)$, $g_{rr}=1/(1-2M/r)$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{tt}=-1/(1-2M/r)$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$ and $g^{\rm EF}_{M,\varepsilon}$ the **Eddington–Finkelstein family** $g^{\rm EF}_{M,\varepsilon}$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(w,r,\theta,\varphi)$ with $w=v$ for $\varepsilon=1$ ingoing and $w=u$ for $\varepsilon=-1$ outgoing): $g_{ww}=-(1-2M/r)$, $g_{wr}=g_{rw}=\varepsilon$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{wr}=\hat g^{rw}=\varepsilon$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, other entries $0$: $$J(x)^{\mathsf T}\,g^{\rm EF}_{M,\varepsilon}\big(\Phi_{M,\varepsilon}(x)\big)\,J(x)=g^{\rm std}_M(x).$$
--
--   Pull-back obligation of relations R1 ($\varepsilon=1$) and R2 ($\varepsilon=-1$); $\det J=1$.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
--
--   **Formalization Note (logarithm).** $\log\lvert r-2M\rvert$ stands for Mathlib's `Real.log (r - 2M)`, which equals $\log\lvert r-2M\rvert$ for every $r\neq2M$ (`Real.log_abs`); the Lean expression is unchanged and the domain is not restricted to $r>2M$.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; Müller–Grave catalogue eq. schwarzschildSpherical (r_s = 2M, G = c = 1); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Schwarzschild/EFPullback.lean#L21-L37 (module Atlas.Schwarzschild.EFPullback, file sha256 f6efed4d3c5874ace673dbcb0f3074b4377453f13641565322c9a762e06eee33; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_EFRelation_pullback.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFCertParts
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.EFRelation
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.EFRelation.pullback (M ε : ℝ) (hε : ε ^ 2 = 1) {x : Pt 4} (hx : x ∈ domStd M) :
    (jac M ε x).transpose * metricMatrix (gEF M ε) (toEF M ε x) * jac M ε x =
      metricMatrix (gStd M) x := by sorry
