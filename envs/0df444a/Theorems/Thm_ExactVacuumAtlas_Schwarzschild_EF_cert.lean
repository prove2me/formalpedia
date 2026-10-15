-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_EF_cert
-- name    : ExactVacuumAtlas.Schwarzschild.EF.cert
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:48:00.526976+00:00
-- url     : https://prove2.me/theorems/220a3aa8-5d55-4127-bc50-f78ab3faf1e8
-- title:
--   Vacuum certificate: Schwarzschild in Eddington–Finkelstein coordinates, both signs, all real $M$
-- statement:
--   Let $M,\varepsilon$ be real numbers with $\varepsilon^2=1$. Consider the **Eddington–Finkelstein family** $g^{\rm EF}_{M,\varepsilon}$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(w,r,\theta,\varphi)$ with $w=v$ for $\varepsilon=1$ ingoing and $w=u$ for $\varepsilon=-1$ outgoing): $g_{ww}=-(1-2M/r)$, $g_{wr}=g_{rw}=\varepsilon$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{wr}=\hat g^{rw}=\varepsilon$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, other entries $0$, on $U^{\rm EF}=\{x:\ r>0,\ 0<\theta<\pi\}$ ($w,\varphi$ arbitrary; for $M>0$ it includes the regular-coordinate portion of $r=2M$ with $0<\theta<\pi$, but not the polar axis, angular identifications or global horizon geometry). Then $$\mathrm{VacuumCertificate}\big(g^{\rm EF}_{M,\varepsilon},\ \hat g^{\rm EF}_{M,\varepsilon},\ U^{\rm EF}\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Parametric form of rows 4 and 5. The Lorentzian frame uses the null block $\begin{pmatrix}-(1-2M/r)&\varepsilon\\\varepsilon&0\end{pmatrix}$ and involves no square root of $1-2M/r$, so it is valid across $r=2M$.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit c36fccb85f270caf981a2bfd2549438988b22880 (contains the 2026-10-13 proof-script fix of EF.cert for the platform 300 s limit; statements unchanged; also at HEAD 0194b9441ce4503d9d9d920b5f42264c78fd0a7c), Atlas/Schwarzschild/EFCert.lean#L20-L42 (module Atlas.Schwarzschild.EFCert, file sha256 fdd9483e959efe66edc0529f73a7cb816ff859a12307df0202c0dd7de49b49d9; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_EF_cert.lean); accepted solution = platform_mirror/Solutions/Sol_ExactVacuumAtlas_Schwarzschild_EF_cert.lean at this commit (sha256 1f9b0e4924681ecf42d19439c579af9be849e1b4a08392dfff250b3cf272e114, submission d3777338-9dde-48ed-8b1b-8eb123d6e9a7 ACCEPTED 2026-10-13)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFCertParts
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.EF
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.EF.cert (M ε : ℝ) (hε : ε ^ 2 = 1) : VacuumCertificate (gEF M ε) (giEF M ε) domEF := by sorry
