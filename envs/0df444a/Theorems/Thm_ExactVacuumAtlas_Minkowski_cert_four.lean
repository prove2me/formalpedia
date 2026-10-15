-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_cert_four
-- name    : ExactVacuumAtlas.Minkowski.cert_four
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:33:28.3611+00:00
-- url     : https://prove2.me/theorems/fe56d42c-2e23-491d-bc0c-8e31b816648b
-- title:
--   Vacuum certificate: Minkowski space in Cartesian coordinates
-- statement:
--   Consider $\eta=\mathrm{diag}(-1,1,1,1)$ as a coordinate metric with constant components on $\mathbb R^4$, the **Cartesian Minkowski metric** $\eta=\mathrm{diag}(-1,1,1,1)$ (bundle `Atlas_Minkowski_Cartesian`, constant components, candidate inverse $\eta$ itself). Then $$\mathrm{VacuumCertificate}\big(\eta,\ \eta,\ \mathbb R^4\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Row 1 of the atlas, the control case: constant metric, vanishing Christoffel symbols; the general-dimension version `Minkowski.cert` is inlined.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eqs. minkCart and minkSph; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/Cartesian.lean#L49-L50 (module Atlas.Minkowski.Cartesian, file sha256 e28e443043a8e2e209d525d5f88daacb33777a03c2df47b8ab5051bdff7c110b; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_cert_four.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Minkowski_Cartesian
open scoped ContDiff

theorem ExactVacuumAtlas.Minkowski.cert_four : VacuumCertificate (gCart 3) (giCart 3) Set.univ := by sorry
