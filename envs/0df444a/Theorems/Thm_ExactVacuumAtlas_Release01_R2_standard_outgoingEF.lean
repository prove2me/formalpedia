-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Release01_R2_standard_outgoingEF
-- name    : ExactVacuumAtlas.Release01.R2_standard_outgoingEF
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:35:53.644771+00:00
-- url     : https://prove2.me/theorems/cf3130c1-d07a-4bee-8651-ec4b0f42bb2d
-- title:
--   R2: standard Schwarzschild to outgoing Eddington–Finkelstein coordinates, all real $M$
-- statement:
--   Let $M$ be an arbitrary real number. With $g^{\rm std}_M$ the **standard Schwarzschild metric** $g^{\rm std}_M$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-(1-2M/r)$, $g_{rr}=1/(1-2M/r)$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{tt}=-1/(1-2M/r)$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, $g^{\rm EF}_{M,-1}$ the **Eddington–Finkelstein family** $g^{\rm EF}_{M,\varepsilon}$ (bundle `Atlas_Schwarzschild_Defs`, coordinates $(w,r,\theta,\varphi)$ with $w=v$ for $\varepsilon=1$ ingoing and $w=u$ for $\varepsilon=-1$ outgoing): $g_{ww}=-(1-2M/r)$, $g_{wr}=g_{rw}=\varepsilon$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, with candidate inverse $\hat g^{wr}=\hat g^{rw}=\varepsilon$, $\hat g^{rr}=1-2M/r$, $\hat g^{\theta\theta}=1/r^2$, $\hat g^{\varphi\varphi}=1/(r^2\sin^2\theta)$, other entries $0$ at $\varepsilon=-1$ ($g_{ur}=-1$), the map $\Phi(t,r,\theta,\varphi)=\big(t-r-2M\log\lvert r-2M\rvert,\ r,\ \theta,\ \varphi\big)$, its inverse $\Psi(u,r,\theta,\varphi)=\big(u+r+2M\log\lvert r-2M\rvert,\ r,\ \theta,\ \varphi\big)$, the Jacobian $J$ with $J_{01}=-\big(1+\frac{2M}{r-2M}\big)$, $J_{ii}=1$ and all other entries $0$, and the overlap $U^{\rm std}_M=\{x:\ r>0,\ r\neq2M,\ 0<\theta<\pi\}$ ($t,\varphi$ arbitrary; for $M>0$ this has an exterior and an interior component): $$\mathrm{CoordRelation}\big(g^{\rm std}_M,\ g^{\rm EF}_{M,-1},\ U^{\rm std}_M,\ U^{\rm std}_M,\ \Phi,\ \Psi,\ J\big).$$ $\mathrm{CoordRelation}(g_1,g_2,U,V,\Phi,\Psi,J)$ (bundle `Atlas_Core_Relation`) asserts: $\Psi(\Phi(x))=x$ for $x\in U$; $\Phi(\Psi(y))=y$ for $y\in V$; $\Phi$ maps $U$ bijectively onto $V$; $\Phi$ is $C^\infty$ on $U$ and $\Psi$ is $C^\infty$ on $V$; for every $x\in U$ and all indices $k,i$ the slice $u\mapsto\Phi(x[x_i:=u])_k$ has derivative $J(x)_{ki}$ at $u=x_i$ (a genuine derivative, not a default value); and $J(x)^{\mathsf T}\,g_2(\Phi(x))\,J(x)=g_1(x)$ for all $x\in U$.
--
--   Relation R2 of the atlas (rows 3 and 5), the outgoing twin of R1.
--
--   **Formalization Note** Everything is coordinate-level on $\mathbb R^4$ (points are functions $\{0,1,2,3\}\to\mathbb R$): no manifold, chart gluing, periodicity of $\varphi$, horizon, causal or global statement is made. Partial derivatives are Mathlib's `deriv` of coordinate slices; the certificates' $C^\infty$ obligations make every derivative used a genuine derivative. Units $G=c=1$, signature $(-,+,+,+)$.
--
--   **Formalization Note (logarithm).** $\log\lvert r-2M\rvert$ stands for Mathlib's `Real.log (r - 2M)`, which equals $\log\lvert r-2M\rvert$ for every $r\neq2M$ (`Real.log_abs`); the Lean expression is unchanged and the domain is not restricted to $r>2M$.
-- source:
--   Müller–Grave catalogue eq. eddFinkel: ds² = −(1−r_s/r) dv² + 2 dv dr + r² dΩ², v = t + r + r_s ln(r − r_s); outgoing form with u = t − r − r_s ln|r − r_s|; Müller–Grave catalogue eq. schwarzschildSpherical (r_s = 2M, G = c = 1); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Release01.lean#L100-L112 (module Atlas.Release01, file sha256 35a31e5ed932c61f239b2a15b3a2a9d8b3ba78368b5b471af95b0ec0e8e73c30; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Release01_R2_standard_outgoingEF.lean)

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

theorem ExactVacuumAtlas.Release01.R2_standard_outgoingEF (M : ℝ) :
    CoordRelation (Schwarzschild.gStd M) (Schwarzschild.gEF M (-1))
      (Schwarzschild.domStd M) (Schwarzschild.domStd M)
      (Schwarzschild.toEF M (-1)) (Schwarzschild.fromEF M (-1))
      (Schwarzschild.EFRelation.jac M (-1)) := by sorry
