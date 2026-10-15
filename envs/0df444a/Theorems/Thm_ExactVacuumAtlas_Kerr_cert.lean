-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_cert
-- name    : ExactVacuumAtlas.Kerr.cert
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:24:57.116945+00:00
-- url     : https://prove2.me/theorems/52ff7aa0-40d4-441a-af72-3d5ac4d10e25
-- title:
--   Vacuum certificate: Kerr in Boyer–Lindquist coordinates, all real $M,a$
-- statement:
--   Let $M,a$ be arbitrary real numbers, $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$. Consider $g^{\rm BL}_{M,a}$, the **Boyer–Lindquist Kerr metric** (platform definition `KerrBL_Kerr_Metric`, coordinates $(t,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$): $g_{tt}=-\big(1-\tfrac{2Mr}{\Sigma}\big)$, $g_{rr}=\tfrac{\Sigma}{\Delta}$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=\big(r^2+a^2+\tfrac{2Ma^2r\sin^2\theta}{\Sigma}\big)\sin^2\theta$, $g_{t\varphi}=g_{\varphi t}=-\tfrac{2Mar\sin^2\theta}{\Sigma}$, other entries $0$, with its closed-form candidate inverse $\hat g$ ($\hat g^{rr}=\Delta/\Sigma$, $\hat g^{\theta\theta}=1/\Sigma$ and a $(t,\varphi)$ block with denominator $\Sigma\Delta\sin^2\theta$), on the regular domain $U^{\rm BL}_{M,a}=\{x:\ \Sigma\neq0,\ \Delta\neq0,\ \sin\theta\neq0\}$. Then $$\mathrm{VacuumCertificate}\big(g^{\rm BL}_{M,a},\ \hat g^{\rm BL}_{M,a},\ U^{\rm BL}_{M,a}\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Row 6 of the atlas. The inverse identity and the vanishing of the sixteen Ricci components are the published, Proved platform theorems `KerrBL.ginv_mul_g_Kerr` and `KerrBL.ricci_flat_Kerr` of the 2026-09 Kerr mission; this certificate adds the open/nonempty domain, symmetry, $C^\infty$ regularity of metric and inverse, and the Lorentzian frame on the whole regular domain with no positivity condition on $\Delta$ (`frameP` where $\Delta>0$, `frameN` where $\Delta<0$). Which signs of $\Delta$ occur depends on $(M,a)$: a negative-$\Delta$ point is exhibited under $a^2<M^2$ in `ExactVacuumAtlas.Release01.coverage`; it is not claimed that both signs occur for every real parameter pair.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/BLCert.lean#L45-L55 (module Atlas.Kerr.BLCert, file sha256 136b56b95b8c5a4cb6ae3c9c48fc15506e3ebab7c1c64911ffa95bcc33268485; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_cert.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Kerr_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff

theorem ExactVacuumAtlas.Kerr.cert (M a : ℝ) : VacuumCertificate (KerrBL.gKerr M a) (KerrBL.giKerr M a) (domBL M a) := by sorry
