-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Kerr_In_cert
-- name    : ExactVacuumAtlas.Kerr.In.cert
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:20:50.622988+00:00
-- url     : https://prove2.me/theorems/5b8a5772-65eb-46f9-a9f9-925b5842a11b
-- title:
--   Vacuum certificate: Kerr in ingoing (Kerr's original) coordinates, all real $M,a$
-- statement:
--   Let $M,a$ be arbitrary real numbers, $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$. Consider the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed), on the domain $U^{\rm in}_a=\{x:\ \Sigma\neq0,\ \sin\theta\neq0\}$ (there is no $\Delta\neq0$ restriction; a point with $\Delta=0$ lies in the domain precisely when it also satisfies $\Sigma\neq0$ and $\sin\theta\neq0$). Then $$\mathrm{VacuumCertificate}\big(g^{\rm in}_{M,a},\ \hat g^{\rm in}_{M,a},\ U^{\rm in}_a\big).$$ $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$.
--
--   Row 7 of the atlas and its hardest case: a non-diagonal metric whose Ricci components vanish only modulo $\sin^2\theta+\cos^2\theta=1$. Here $v$ is an advanced-type coordinate: the radial coordinate vector $\partial_r$ is null ($g_{rr}=0$), whereas for $a\neq0$ the covector $dv$ is not null, since $\hat g^{vv}=a^2\sin^2\theta/\Sigma\neq0$ on the domain (where $\hat g$ is the inverse by this certificate); no claim is made that the hypersurfaces $v=\text{const}$ are null. There is no $\Delta\neq0$ restriction, which Boyer–Lindquist coordinates need: the certificate applies at points with $\Delta=0$ precisely where $\Sigma\neq0$ and $\sin\theta\neq0$ also hold, and `ExactVacuumAtlas.Release01.coverage` supplies such a point in the sufficient parameter regime $M>0$, $a^2\le M^2$. The certificate itself assumes no positivity of $M$ and no bound on $a$.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Kerr/InCert.lean#L27-L37 (module Atlas.Kerr.InCert, file sha256 e19e18dcd4c7fc10a5ff849845d78c072b9d8dbc750e80674f004d959b1c535b; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Kerr_In_cert.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
import Definitions.Def_Atlas_Kerr_InParts
open scoped ContDiff

theorem ExactVacuumAtlas.Kerr.In.cert (M a : ℝ) : VacuumCertificate (gIn M a) (giIn M a) (domIn a) := by sorry
