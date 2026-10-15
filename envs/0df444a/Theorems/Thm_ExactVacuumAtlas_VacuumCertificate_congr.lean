-- Prove2me | Theorems.Thm_ExactVacuumAtlas_VacuumCertificate_congr
-- name    : ExactVacuumAtlas.VacuumCertificate.congr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:32:41.457301+00:00
-- url     : https://prove2.me/theorems/0927b064-3284-4db2-bb66-fafe4775c352
-- title:
--   Vacuum certificates transport along metrics that agree on the domain
-- statement:
--   Let $n$ be a natural number, $g,\hat g$ coordinate metrics on $\mathbb R^{n+1}$, $U\subseteq\mathbb R^{n+1}$, and suppose $\mathrm{VacuumCertificate}(g,\hat g,U)$. If $g',\hat g'$ are coordinate metrics with $g'_{ij}=g_{ij}$ and $\hat g'_{ij}=\hat g_{ij}$ pointwise on $U$ for all $i,j$, then $\mathrm{VacuumCertificate}(g',\hat g',U)$. $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_{n+1}$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\eta_n=\mathrm{diag}(-1,1,\dots,1)$ with $n$ entries $+1$ (Lorentzian signature); and all $(n+1)^2$ ordered components $R_{bd}(x)$, $b,d\in\{0,\dots,n\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Lets a certificate proved for one presentation of the data be reused for another presentation equal on the domain (Minkowski spherical = Schwarzschild at $M=0$; standard Schwarzschild = Boyer–Lindquist Kerr at $a=0$). Since the Ricci tensor is built from slice derivatives, the agreement on the open set $U$ suffices. This is equality-based transport on the same domain in total dimension $n+1$, not coordinate-covariance transport.
--
--   **Formalization Note** Dimension $n+1$; agreement is `Set.EqOn` on $U$ for every component.
-- source:
--   coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Certificate.lean#L75-L96 (module Atlas.Core.Certificate, file sha256 c714a637b0dab5004e0072ce4fd3c4e7033c9c1289d2e934626cb506d5eaefe3; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_VacuumCertificate_congr.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ} {g ginv : Metric (n + 1)} {U : Set (Pt (n + 1))}

theorem ExactVacuumAtlas.VacuumCertificate.congr (h : VacuumCertificate g ginv U) {g' ginv' : Metric (n + 1)}
    (hg : ∀ i j, Set.EqOn (g i j) (g' i j) U) (hgi : ∀ i j, Set.EqOn (ginv i j) (ginv' i j) U) :
    VacuumCertificate g' ginv' U := by sorry
