-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_certSph
-- name    : ExactVacuumAtlas.Minkowski.certSph
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:32:51.32542+00:00
-- url     : https://prove2.me/theorems/f74b45e9-5712-4318-818f-091313d821c0
-- title:
--   Vacuum certificate: Minkowski space in spherical coordinates
-- statement:
--   Consider $g^{\rm sph}$, the **spherical Minkowski metric** $g^{\rm sph}$ (bundle `Atlas_Minkowski_Spherical`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-1$, $g_{rr}=1$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, candidate inverse $\mathrm{diag}(-1,1,1/r^2,1/(r^2\sin^2\theta))$, on $U^{\rm sph}=\{x:\ r>0,\ 0<\theta<\pi\}$ ($t,\varphi$ arbitrary). Then $$\mathrm{VacuumCertificate}\big(g^{\rm sph},\ \hat g^{\rm sph},\ U^{\rm sph}\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Row 2 of the atlas; obtained from the standard Schwarzschild certificate at $M=0$ by transport along the equality of the two metrics on the domain.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eqs. minkCart and minkSph; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/Spherical.lean#L50-L53 (module Atlas.Minkowski.Spherical, file sha256 ab4b8959cd1ac9b6b83f657f27f3300b2e02cd2984faf598e05b2b6b51035b1f; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_certSph.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open ExactVacuumAtlas
open ExactVacuumAtlas.Minkowski
open ExactVacuumAtlas.Schwarzschild

theorem ExactVacuumAtlas.Minkowski.certSph : VacuumCertificate gSph giSph domSph := by sorry
