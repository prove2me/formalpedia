-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release01_main
-- name    : ExactVacuumAtlas.Release01.main
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:51:15.508244+00:00
-- url     : https://prove2.me/theorems/76d9e288-b930-4203-a3ba-d9dacaa2884a
-- title:
--   Exact Vacuum Atlas I: seven vacuum certificates and four coordinate relations
-- statement:
--   Points of $\mathbb R^4$ are written $x=(x_0,x_1,x_2,x_3)$; a coordinate metric is a $4\times4$ matrix $g=(g_{ij})$ of real functions of $x$, and a *candidate inverse* $\hat g$ is another such matrix. $\mathrm{VacuumCertificate}(g,\hat g,U)$ (bundle `Atlas_Core_Certificate`) is the conjunction of eight obligations: $U$ is open and nonempty; $g_{ij}(x)=g_{ji}(x)$ for $x\in U$; $\hat g(x)\,g(x)=I_4$ for every $x\in U$; every component of $g$ and of $\hat g$ is $C^\infty$ on $U$; at every $x\in U$ there is an invertible matrix $E$ with $E^{\mathsf T}g(x)E=\mathrm{diag}(-1,1,1,1)$ (Lorentzian signature); and all sixteen components $R_{bd}(x)$, $b,d\in\{0,1,2,3\}$, of the coordinate Ricci tensor built from $g$ and $\hat g$ vanish for $x\in U$. $\mathrm{CoordRelation}(g_1,g_2,U,V,\Phi,\Psi,J)$ (bundle `Atlas_Core_Relation`) asserts: $\Psi(\Phi(x))=x$ for $x\in U$; $\Phi(\Psi(y))=y$ for $y\in V$; $\Phi$ maps $U$ bijectively onto $V$; $\Phi$ is $C^\infty$ on $U$ and $\Psi$ is $C^\infty$ on $V$; for every $x\in U$ and all indices $k,i$ the slice $u\mapsto\Phi(x[x_i:=u])_k$ has derivative $J(x)_{ki}$ at $u=x_i$ (a genuine derivative, not a default value); and $J(x)^{\mathsf T}\,g_2(\Phi(x))\,J(x)=g_1(x)$ for all $x\in U$. The theorem is the conjunction of eleven statements.
--
--   **Seven vacuum certificates** (all parameters arbitrary reals; $\Sigma=r^2+a^2\cos^2\theta$, $\Delta=r^2-2Mr+a^2$):
--
--   1. $\mathrm{VacuumCertificate}(\eta,\eta,\mathbb R^4)$ for the **Cartesian Minkowski metric** $\eta=\mathrm{diag}(-1,1,1,1)$ (bundle `Atlas_Minkowski_Cartesian`, constant components, candidate inverse $\eta$ itself);
--   2. $\mathrm{VacuumCertificate}(g^{\rm sph},\hat g^{\rm sph},\{r>0,0<\theta<\pi\})$ for the **spherical Minkowski metric** $g^{\rm sph}$ (bundle `Atlas_Minkowski_Spherical`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-1$, $g_{rr}=1$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, candidate inverse $\mathrm{diag}(-1,1,1/r^2,1/(r^2\sin^2\theta))$;
--   3. $\forall M$: $\mathrm{VacuumCertificate}(g^{\rm std}_M,\hat g^{\rm std}_M,\{r>0,r\neq2M,0<\theta<\pi\})$ for the **standard Schwarzschild metric** $g^{\rm std}_M$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-(1-2M/r)$, $g_{rr}=1/(1-2M/r)$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{tt}=-1/(1-2M/r)$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$;
--   4. $\forall M$: $\mathrm{VacuumCertificate}(g^{\rm EF}_{M,1},\hat g^{\rm EF}_{M,1},\{r>0,0<\theta<\pi\})$ (ingoing, $g_{vr}=1$) for the **Eddington–Finkelstein family** $g^{\rm EF}_{M,\varepsilon}$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(w,r,\theta,\varphi)$ with $w=v$ for $\varepsilon=1$ ingoing and $w=u$ for $\varepsilon=-1$ outgoing): $g_{ww}=-(1-2M/r)$, $g_{wr}=g_{rw}=\varepsilon$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{wr}=\hat g^{rw}=\varepsilon$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, other entries $0$;
--   5. $\forall M$: $\mathrm{VacuumCertificate}(g^{\rm EF}_{M,-1},\hat g^{\rm EF}_{M,-1},\{r>0,0<\theta<\pi\})$ (outgoing, $g_{ur}=-1$);
--   6. $\forall M,a$: $\mathrm{VacuumCertificate}(g^{\rm BL}_{M,a},\hat g^{\rm BL}_{M,a},\{\Sigma\neq0,\Delta\neq0,\sin\theta\neq0\})$ for the **Boyer–Lindquist Kerr metric** (platform definition `KerrBL_Kerr_Metric`, coordinates $(t,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$): $g_{tt}=-\big(1-\tfrac{2Mr}{\Sigma}\big)$, $g_{rr}=\tfrac{\Sigma}{\Delta}$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=\big(r^2+a^2+\tfrac{2Ma^2r\sin^2\theta}{\Sigma}\big)\sin^2\theta$, $g_{t\varphi}=g_{\varphi t}=-\tfrac{2Mar\sin^2\theta}{\Sigma}$, other entries $0$, with its closed-form candidate inverse $\hat g$ ($\hat g^{rr}=\Delta/\Sigma$, $\hat g^{\theta\theta}=1/\Sigma$ and a $(t,\varphi)$ block with denominator $\Sigma\Delta\sin^2\theta$);
--   7. $\forall M,a$: $\mathrm{VacuumCertificate}(g^{\rm in}_{M,a},\hat g^{\rm in}_{M,a},\{\Sigma\neq0,\sin\theta\neq0\})$ for the **ingoing (Kerr's original, advanced) Kerr metric** $g^{\rm in}$ of bundle `Atlas_Kerr_InDefs`, read off from Visser's line element $ds^2=-F\,(dv+a\sin^2\theta\,d\varphi)^2+2\,(dv+a\sin^2\theta\,d\varphi)(dr+a\sin^2\theta\,d\varphi)+\Sigma\,(d\theta^2+\sin^2\theta\,d\varphi^2)$, $F=1-2Mr/\Sigma$, with the half-Hessian convention ($g_{vr}=1$): in coordinates $(v,r,\theta,\varphi)=(x_0,x_1,x_2,x_3)$ and with $A=a\sin^2\theta$, $g_{vv}=-F$, $g_{vr}=g_{rv}=1$, $g_{v\varphi}=g_{\varphi v}=(1-F)A$, $g_{r\varphi}=g_{\varphi r}=A$, $g_{\theta\theta}=\Sigma$, $g_{\varphi\varphi}=(2-F)A^2+\Sigma\sin^2\theta$, all remaining entries $0$; its candidate inverse $\hat g^{\rm in}$ has $\hat g^{vv}=a^2\sin^2\theta/\Sigma$, $\hat g^{vr}=\hat g^{rv}=(r^2+a^2)/\Sigma$, $\hat g^{v\varphi}=\hat g^{\varphi v}=\hat g^{r\varphi}=\hat g^{\varphi r}=-a/\Sigma$, $\hat g^{rr}=\Delta/\Sigma$ with $\Delta=r^2-2Mr+a^2$, $\hat g^{\theta\theta}=1/\Sigma$, $\hat g^{\varphi\varphi}=1/(\Sigma\sin^2\theta)$, all remaining entries $0$ (both matrices are symmetric; every symmetric counterpart is listed).
--
--   **Four coordinate relations**, each with its explicit map, inverse, overlap/image and Jacobian:
--
--   8. R1, $\forall M$: standard Schwarzschild to ingoing EF, $\Phi(t,r,\theta,\varphi)=(t+r+2M\log\lvert r-2M\rvert,r,\theta,\varphi)$ on $U=V=\{r>0,r\neq2M,0<\theta<\pi\}$, $J_{01}=1+\frac{2M}{r-2M}$;
--   9. R2, $\forall M$: standard Schwarzschild to outgoing EF, $\Phi=(t-r-2M\log\lvert r-2M\rvert,r,\theta,\varphi)$, same overlap, $J_{01}=-(1+\frac{2M}{r-2M})$;
--   10. R3, $\forall M,a$: Boyer–Lindquist to ingoing Kerr, $\Phi=(t+r+H_1(r),r,\theta,-\varphi-H_2(r))$ with the explicit $H_1=M\log|\Delta|+2M^2K$, $H_2=aK$ ($K'=1/\Delta$ in all three branches of $M^2-a^2$), on $U=V=\{\Sigma\neq0,\Delta\neq0,\sin\theta\neq0\}$, $J$ with rows $(1,\frac{r^2+a^2}\Delta,0,0),(0,1,0,0),(0,0,1,0),(0,-\frac a\Delta,0,-1)$;
--   11. R4: spherical chart $\{r>0,0<\theta<\pi,0<\varphi<2\pi\}$ to Cartesian $\mathbb R^4\setminus\{y=0,x\ge0\}$, $\Phi=(t,r\sin\theta\cos\varphi,r\sin\theta\sin\varphi,r\cos\theta)$ with its explicit inverse and Jacobian.
--
--   $$\textstyle\bigwedge_{k=1}^{7}\mathrm{Cert}_k\ \wedge\ \mathrm{R1}\wedge\mathrm{R2}\wedge\mathrm{R3}\wedge\mathrm{R4}.$$
--
--   The goal theorem of the mission: a machine-checked coordinate-level atlas of the three basic vacuum solutions in seven standard forms on explicit open domains (no domain condition excludes the Schwarzschild interior $0<r<2M$ for $M>0$, either sign of $\Delta$ or negative $r$ for Kerr, the regular-coordinate portion of $r=2M$ with $0<\theta<\pi$ for $M>0$ (Eddington–Finkelstein), or the points with $\Delta=0$ at which $\Sigma\neq0$ and $\sin\theta\neq0$ (ingoing Kerr); `ExactVacuumAtlas.Release01.coverage` exhibits points with $r=2M$, $\Delta<0$ and $\Delta=0$ under its sufficient parameter conditions, and it is not claimed that every parameter pair has points of each kind; the polar axis, angular identifications and global horizon geometry are not included), with the four changes of coordinates proved as explicit maps rather than existence statements. It only assembles the seven certificates and four relations proved as separate nodes. Not contained: any manifold, atlas-gluing, horizon, causal, maximal-extension or classification statement, any coordinate-covariance theorem for the coordinate Ricci tensor, or any relation to a manifold Ricci tensor of Mathlib (none exists in the pinned version).
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eqs. minkCart and minkSph; Müller–Grave catalogue eq. schwarzschildSpherical (r_s = 2M, G = c = 1); Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; R. P. Kerr, Phys. Rev. Lett. 11 (1963) 237, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer, R. W. Lindquist, J. Math. Phys. 8 (1967) 265, https://doi.org/10.1063/1.1705193; Müller–Grave catalogue eq. kerrBLbardeen; metric data = platform definition KerrBL_Kerr_Metric (id 8b2152c1-375e-4302-8acf-50c30d42d46d); M. Visser, arXiv:0706.0622, eq. (E:K1) (Survey-grqc-3.tex lines 205–215), Visser's u renamed v; M. Visser, arXiv:0706.0622, eqs. (E:BL-change-1), (E:BL-change-2), (E:BL-change-3): u = t + r, t = t_BL + 2M∫ r dr/Δ, φ = −φ_BL − a∫ dr/Δ; coordinate Christoffel symbols and Ricci tensor: Müller–Grave catalogue.tex lines 277–281 (eq. ChristoffelSymbols), 287–290 (eq. RiemannTensor), 305–307 (R_{μν}=R^ρ_{μρν}), verified by the independent review 2026-10-13; R. M. Wald, General Relativity (1984) eqs. (3.1.30), (3.4.4)–(3.4.5) author-cited (not reviewer-verified); same formulas as platform definition KerrBL_CoordGeometry (id bbec007a-159a-4623-916d-f1cafab3e353); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Release01.lean#L142-L174 (module Atlas.Release01, file sha256 35a31e5ed932c61f239b2a15b3a2a9d8b3ba78368b5b471af95b0ec0e8e73c30; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Release01_main.lean)

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

theorem ExactVacuumAtlas.Release01.main :
    -- rows 1–7
    VacuumCertificate (Minkowski.gCart 3) (Minkowski.giCart 3) (Set.univ : Set (Pt 4)) ∧
    VacuumCertificate Minkowski.gSph Minkowski.giSph Minkowski.domSph ∧
    (∀ M : ℝ, VacuumCertificate (Schwarzschild.gStd M) (Schwarzschild.giStd M)
      (Schwarzschild.domStd M)) ∧
    (∀ M : ℝ, VacuumCertificate (Schwarzschild.gEF M 1) (Schwarzschild.giEF M 1)
      Schwarzschild.domEF) ∧
    (∀ M : ℝ, VacuumCertificate (Schwarzschild.gEF M (-1)) (Schwarzschild.giEF M (-1))
      Schwarzschild.domEF) ∧
    (∀ M a : ℝ, VacuumCertificate (KerrBL.gKerr M a) (KerrBL.giKerr M a) (Kerr.domBL M a)) ∧
    (∀ M a : ℝ, VacuumCertificate (Kerr.In.gIn M a) (Kerr.In.giIn M a) (Kerr.In.domIn a)) ∧
    -- relations R1–R4
    (∀ M : ℝ, CoordRelation (Schwarzschild.gStd M) (Schwarzschild.gEF M 1)
      (Schwarzschild.domStd M) (Schwarzschild.domStd M)
      (Schwarzschild.toEF M 1) (Schwarzschild.fromEF M 1) (Schwarzschild.EFRelation.jac M 1)) ∧
    (∀ M : ℝ, CoordRelation (Schwarzschild.gStd M) (Schwarzschild.gEF M (-1))
      (Schwarzschild.domStd M) (Schwarzschild.domStd M)
      (Schwarzschild.toEF M (-1)) (Schwarzschild.fromEF M (-1))
      (Schwarzschild.EFRelation.jac M (-1))) ∧
    (∀ M a : ℝ, CoordRelation (KerrBL.gKerr M a) (Kerr.In.gIn M a)
      (Kerr.domBL M a) (Kerr.domBL M a)
      (Kerr.R3.toIn (Kerr.R3.H1 M a) (Kerr.R3.H2 M a))
      (Kerr.R3.fromIn (Kerr.R3.H1 M a) (Kerr.R3.H2 M a)) (Kerr.R3.jac M a)) ∧
    CoordRelation Minkowski.gSph (Minkowski.gCart 3) Minkowski.R4.domChart Minkowski.R4.imgCart
      Minkowski.R4.toCart Minkowski.R4.fromCart Minkowski.R4.jac := by sorry
