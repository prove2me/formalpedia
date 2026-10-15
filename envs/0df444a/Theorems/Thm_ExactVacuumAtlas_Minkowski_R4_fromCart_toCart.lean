-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_R4_fromCart_toCart
-- name    : ExactVacuumAtlas.Minkowski.R4.fromCart_toCart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:27:53.622544+00:00
-- url     : https://prove2.me/theorems/0d3ec27c-dabd-4e63-a0d6-30c21cbbed48
-- title:
--   Spherical chart: the Cartesian map is inverted on the chart
-- statement:
--   Let $\Phi(t,r,\theta,\varphi)=(t,\ r\sin\theta\cos\varphi,\ r\sin\theta\sin\varphi,\ r\cos\theta)$ and $\Psi$ the inverse map of bundle `Atlas_Minkowski_R4` ($\rho=\sqrt{x^2+y^2+z^2}$, $\theta=\arccos(z/\rho)$, $\varphi=\pi+2\arctan\big(-y/(\sqrt{x^2+y^2}-x)\big)$). For every $x=(t,r,\theta,\varphi)$ in the chart $U=\{r>0,\ 0<\theta<\pi,\ 0<\varphi<2\pi\}$, $$\Psi(\Phi(x))=x.$$
--
--   Left-inverse obligation of relation R4.
-- source:
--   elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/R4.lean#L155-L210 (module Atlas.Minkowski.R4, file sha256 a1fc97dfc0dd15a14ffbb8dfbee1cfe1421e5f3119a6b8607bb683d8caafc495; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_R4_fromCart_toCart.lean)

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

theorem ExactVacuumAtlas.Minkowski.R4.fromCart_toCart {x : Pt 4} (hx : x ∈ domChart) : fromCart (toCart x) = x := by sorry
