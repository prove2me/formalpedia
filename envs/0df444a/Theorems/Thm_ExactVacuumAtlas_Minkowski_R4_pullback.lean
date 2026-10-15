-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_R4_pullback
-- name    : ExactVacuumAtlas.Minkowski.R4.pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:30:33.68606+00:00
-- url     : https://prove2.me/theorems/3be113b1-5dd6-4000-807e-ce8df936b3e6
-- title:
--   Spherical Minkowski metric is the pull-back of the Cartesian one
-- statement:
--   Let $\Phi$ and $J$ be the spherical-to-Cartesian map and its Jacobian matrix (bundle `Atlas_Minkowski_R4`), $\eta=\mathrm{diag}(-1,1,1,1)$ the **Cartesian Minkowski metric** $\eta=\mathrm{diag}(-1,1,1,1)$ (bundle `Atlas_Minkowski_Cartesian`, constant components, candidate inverse $\eta$ itself), and $g^{\rm sph}$ the **spherical Minkowski metric** $g^{\rm sph}$ (bundle `Atlas_Minkowski_Spherical`, coordinates $(t,r,\theta,\varphi)$): $g_{tt}=-1$, $g_{rr}=1$, $g_{\theta\theta}=r^2$, $g_{\varphi\varphi}=r^2\sin^2\theta$, other entries $0$, candidate inverse $\mathrm{diag}(-1,1,1/r^2,1/(r^2\sin^2\theta))$. For every $x$ in the chart $\{r>0,\ 0<\theta<\pi,\ 0<\varphi<2\pi\}$, $$J(x)^{\mathsf T}\,\eta\,J(x)=g^{\rm sph}(x).$$
--
--   Pull-back obligation of relation R4; it holds for all $x$, the chart hypothesis being carried only for uniformity with the relation bundle.
-- source:
--   Müller–Grave catalogue eqs. minkCart and minkSph; elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/R4.lean#L400-L414 (module Atlas.Minkowski.R4, file sha256 a1fc97dfc0dd15a14ffbb8dfbee1cfe1421e5f3119a6b8607bb683d8caafc495; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_R4_pullback.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Minkowski_Cartesian
import Definitions.Def_Atlas_Minkowski_R4
import Definitions.Def_Atlas_Minkowski_Spherical
import Definitions.Def_Atlas_Schwarzschild_Defs
import Definitions.Def_Atlas_Schwarzschild_Domain
import Definitions.Def_Atlas_Schwarzschild_StdParts
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.Minkowski
open ExactVacuumAtlas
open ExactVacuumAtlas.Minkowski
open ExactVacuumAtlas.Minkowski.R4
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem ExactVacuumAtlas.Minkowski.R4.pullback {x : Pt 4} (_hx : x ∈ domChart) :
    (jac x).transpose * metricMatrix (gCart 3) (toCart x) * jac x = metricMatrix gSph x := by sorry
