-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Schwarzschild_Std_cert
-- name    : ExactVacuumAtlas.Schwarzschild.Std.cert
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:31:49.869541+00:00
-- url     : https://prove2.me/theorems/2fa2506a-b9a3-4c0e-b78a-45e66f480d23
-- title:
--   Vacuum certificate: Schwarzschild in standard coordinates, all real $M$
-- statement:
--   Let $M$ be an arbitrary real number. Consider $g^{\rm std}_M$, the **standard Schwarzschild metric** $g^{\rm std}_M$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-(1-2M/r)$, $g_{rr}=1/(1-2M/r)$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{tt}=-1/(1-2M/r)$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, on $U^{\rm std}_M=\{x:\ r>0,\ r\neq2M,\ 0<\theta<\pi\}$ ($t,\varphi$ arbitrary; for $M>0$ this has an exterior and an interior component). Then $$\mathrm{VacuumCertificate}\big(g^{\rm std}_M,\ \hat g^{\rm std}_M,\ U^{\rm std}_M\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Row 3 of the atlas. Ricci-flatness is reused from the published Boyer–Lindquist result `KerrBL.ricci_flat_Kerr` at $a=0$ through proved componentwise equalities of the metric data on the open domain and locality of the coordinate Ricci tensor; the remaining certificate obligations (domain, symmetry, inverse, smoothness, frame) are supplied separately. No sign of $M$ is assumed.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eq. schwarzschildSpherical (r_s = 2M, G = c = 1); coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Schwarzschild/StdCert.lean#L64-L78 (module Atlas.Schwarzschild.StdCert, file sha256 af33bb6c24af47532c603f4130fa033f22bfd853620a67c4f6b1b62c7014a1b4; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Schwarzschild_Std_cert.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas
open ExactVacuumAtlas.Schwarzschild
open ExactVacuumAtlas.Schwarzschild.Std
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.Schwarzschild.Std.cert (M : ℝ) : VacuumCertificate (gStd M) (giStd M) (domStd M) := by sorry
