-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release01_R3_boyerLindquist_ingoing
-- name    : ExactVacuumAtlas.Release01.R3_boyerLindquist_ingoing
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:35:40.156816+00:00
-- url     : https://prove2.me/theorems/67c00cfb-c4bd-4c6a-ac8e-d38e3d513959
-- title:
--   R3: Boyer–Lindquist to ingoing Kerr coordinates with explicit antiderivatives, all real $M,a$
-- statement:
--   Let $M,a$ be arbitrary real numbers, $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$. Let $K=K_{M,a}$ be the explicit antiderivative of $1/\Delta$ (two real roots: logarithms; double root: $-1/(r-M)$; no real root: arctangent), $H_1(r)=M\log|\Delta(r)|+2M^2K(r)$ and $H_2(r)=aK(r)$, so that $H_1'=2Mr/\Delta$ and $H_2'=a/\Delta$ off the roots. With $g^{\rm BL}_{M,a}$ the **Boyer–Lindquist Kerr metric** (platform definition `KerrBL_Kerr_Metric`, coordinates $(t,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$): $g_{tt}=-\big(1-\tfrac{2Mr}{\Sigma}\big)$, $g_{rr}=\tfrac{\Sigma}{\Delta}$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=\big(r^2+a^2+\tfrac{2Ma^2r\sin^2\theta}{\Sigma}\big)\sin^2\theta$, $g_{t\varphi}=g_{\varphi t}=-\tfrac{2Mar\sin^2\theta}{\Sigma}$, other entries $0$, with its closed-form candidate inverse $\hat g$ ($\hat g^{rr}=\Delta/\Sigma$, $\hat g^{\theta\theta}=1/\Sigma$ and a $(t,\varphi)$ block with denominator $\Sigma\Delta\sin^2\theta$), $g^{\rm in}_{M,a}$ the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed), the map $$\Phi(t,r,\theta,\varphi)=\big(t+r+H_1(r),\ r,\ \theta,\ -\varphi-H_2(r)\big),$$ its inverse $\Psi(v,r,\theta,\tilde\varphi)=\big(v-r-H_1(r),\ r,\ \theta,\ -\tilde\varphi-H_2(r)\big)$, the Jacobian $J$ with rows $(1,\frac{r^2+a^2}{\Delta},0,0)$, $(0,1,0,0)$, $(0,0,1,0)$, $(0,-\frac a\Delta,0,-1)$, and the overlap $U^{\rm BL}_{M,a}=\{x:\ \Sigma\neq0,\ \Delta\neq0,\ \sin\theta\neq0\}$ (mapped onto itself): $$\mathrm{CoordRelation}\big(g^{\rm BL}_{M,a},\ g^{\rm in}_{M,a},\ U^{\rm BL}_{M,a},\ U^{\rm BL}_{M,a},\ \Phi,\ \Psi,\ J\big).$$ $\mathrm{CoordRelation}(g_1,g_2,U,V,\Phi,\Psi,J)$ (bundle `Atlas_Core_Relation`) asserts: $\Psi(\Phi(x))=x$ for $x\in U$; $\Phi(\Psi(y))=y$ for $y\in V$; $\Phi$ maps $U$ bijectively onto $V$; $\Phi$ is $C^\infty$ on $U$ and $\Psi$ is $C^\infty$ on $V$; for every $x\in U$ and all indices $k,i$ the slice $u\mapsto\Phi(x[x_i:=u])_k$ has derivative $J(x)_{ki}$ at $u=x_i$ (a genuine derivative, not a default value); and $J(x)^{\mathsf T}\,g_2(\Phi(x))\,J(x)=g_1(x)$ for all $x\in U$.
--
--   Relation R3 of the atlas (rows 6 and 7), Visser's change of coordinates with the integrals made explicit for every real $M,a$; $\det J=-1$. The overlap is the Boyer–Lindquist regular domain, a subset of the ingoing domain; points with $\Delta=0$ are covered by row 7 alone, at those points where $\Sigma\neq0$ and $\sin\theta\neq0$ also hold.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   M. Visser, arXiv:0706.0622, eqs. (E:BL-change-1), (E:BL-change-2), (E:BL-change-3): u = t + r, t = t_BL + 2M∫ r dr/Δ, φ = −φ_BL − a∫ dr/Δ; R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Release01.lean#L114-L126 (module Atlas.Release01, file sha256 35a31e5ed932c61f239b2a15b3a2a9d8b3ba78368b5b471af95b0ec0e8e73c30; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Release01_R3_boyerLindquist_ingoing.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Kerr_Domain
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Kerr_InDefs
import Definitions.Def_Atlas_Kerr_InParts
import Definitions.Def_Atlas_Kerr_R3
import Definitions.Def_Atlas_Minkowski_Cartesian
import Definitions.Def_Atlas_Minkowski_R4
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_EFCertParts
import Definitions.Def_Atlas_Schwarzschild_EFRelation
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open scoped ContDiff

theorem ExactVacuumAtlas.Release01.R3_boyerLindquist_ingoing (M a : ℝ) :
    CoordRelation (KerrBL.gKerr M a) (Kerr.In.gIn M a) (Kerr.domBL M a) (Kerr.domBL M a)
      (Kerr.R3.toIn (Kerr.R3.H1 M a) (Kerr.R3.H2 M a))
      (Kerr.R3.fromIn (Kerr.R3.H1 M a) (Kerr.R3.H2 M a)) (Kerr.R3.jac M a) := by sorry
