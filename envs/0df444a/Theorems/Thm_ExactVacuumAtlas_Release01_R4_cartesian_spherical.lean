-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release01_R4_cartesian_spherical
-- name    : ExactVacuumAtlas.Release01.R4_cartesian_spherical
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:37:02.098988+00:00
-- url     : https://prove2.me/theorems/fdf0e556-f9e4-4ce1-bb04-93da5efcf513
-- title:
--   R4: spherical chart to Cartesian coordinates of Minkowski space
-- statement:
--   Let $g^{\rm sph}$ be the **spherical Minkowski metric** $g^{\rm sph}$ (bundle `Atlas_Minkowski_Spherical`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-1$, $g_{rr}=1$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, candidate inverse $\mathrm{diag}(-1,1,1/r^2,1/(r^2\sin^2\theta))$ and $\eta$ the **Cartesian Minkowski metric** $\eta=\mathrm{diag}(-1,1,1,1)$ (bundle `Atlas_Minkowski_Cartesian`, constant components, candidate inverse $\eta$ itself). Let $U=\{r>0,\ 0<\theta<\pi,\ 0<\varphi<2\pi\}$, $V=\{(t,x,y,z):\ \neg(y=0\wedge x\ge0)\}$, $\Phi(t,r,\theta,\varphi)=(t,\ r\sin\theta\cos\varphi,\ r\sin\theta\sin\varphi,\ r\cos\theta)$, $\Psi(t,x,y,z)=\big(t,\rho,\arccos(z/\rho),\pi+2\arctan\frac{-y}{\sqrt{x^2+y^2}-x}\big)$ with $\rho=\sqrt{x^2+y^2+z^2}$, and $J$ the Jacobian matrix of $\Phi$ ($\det J=r^2\sin\theta$). Then $$\mathrm{CoordRelation}\big(g^{\rm sph},\ \eta,\ U,\ V,\ \Phi,\ \Psi,\ J\big).$$ $\mathrm{CoordRelation}(g_1,g_2,U,V,\Phi,\Psi,J)$ (bundle `Atlas_Core_Relation`) asserts: $\Psi(\Phi(x))=x$ for $x\in U$; $\Phi(\Psi(y))=y$ for $y\in V$; $\Phi$ maps $U$ bijectively onto $V$; $\Phi$ is $C^\infty$ on $U$ and $\Psi$ is $C^\infty$ on $V$; for every $x\in U$ and all indices $k,i$ the slice $u\mapsto\Phi(x[x_i:=u])_k$ has derivative $J(x)_{ki}$ at $u=x_i$ (a genuine derivative, not a default value); and $J(x)^{\mathsf T}\,g_2(\Phi(x))\,J(x)=g_1(x)$ for all $x\in U$.
--
--   Relation R4 of the atlas (rows 2 and 1) on one chart $\varphi\in(0,2\pi)$; the identification $\varphi\sim\varphi+2\pi$ is not modelled.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
-- source:
--   Müller–Grave catalogue eqs. minkCart and minkSph; elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Release01.lean#L128-L138 (module Atlas.Release01, file sha256 35a31e5ed932c61f239b2a15b3a2a9d8b3ba78368b5b471af95b0ec0e8e73c30; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Release01_R4_cartesian_spherical.lean)

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

theorem ExactVacuumAtlas.Release01.R4_cartesian_spherical :
    CoordRelation Minkowski.gSph (Minkowski.gCart 3) Minkowski.R4.domChart Minkowski.R4.imgCart
      Minkowski.R4.toCart Minkowski.R4.fromCart Minkowski.R4.jac := by sorry
