-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_R4_contDiffOn_fromCart
-- name    : ExactVacuumAtlas.Minkowski.R4.contDiffOn_fromCart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:25:18.520754+00:00
-- url     : https://prove2.me/theorems/22f25b3a-49f0-4fa1-bea7-2fd1ff02692c
-- title:
--   Cartesian to spherical coordinates: the inverse map is smooth off the slit half-plane
-- statement:
--   Let $\Psi:\mathbb R^4\to\mathbb R^4$ be $$\Psi(t,x,y,z)=\Big(t,\ \rho,\ \arccos\frac z\rho,\ \pi+2\arctan\frac{-y}{\sqrt{x^2+y^2}-x}\Big),\qquad \rho=\sqrt{x^2+y^2+z^2},$$ and let $V=\{(t,x,y,z):\ \neg(y=0\wedge x\ge0)\}$ be the complement of the closed half-plane $\{y=0,\ x\ge0\}$. Then $\Psi$ is $C^\infty$ on $V$.
--
--   Smoothness of the inverse in relation R4 (spherical chart $\varphi\in(0,2\pi)$ to Cartesian coordinates); the half-angle formula for $\varphi$ avoids the discontinuity of the two-argument arctangent on the slit.
--
--   **Formalization Note** $\arccos$, $\arctan$ and $\sqrt{\cdot}$ are Mathlib's total real functions; the domain $V$ excludes the entire spatial $z$-axis (every point with $x=y=0$ satisfies $y=0\wedge x\ge0$), together with the rest of the chosen azimuthal slit $\{y=0,\ x\ge0\}$. On $V$ one has $x^2+y^2>0$, hence $\rho>0$, $\sqrt{x^2+y^2}-x>0$ and $\lvert z/\rho\rvert<1$, so the displayed inverse-coordinate formulas are used away from their singular and endpoint cases.
-- source:
--   elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/R4.lean#L283-L312 (module Atlas.Minkowski.R4, file sha256 a1fc97dfc0dd15a14ffbb8dfbee1cfe1421e5f3119a6b8607bb683d8caafc495; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_R4_contDiffOn_fromCart.lean)

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

theorem ExactVacuumAtlas.Minkowski.R4.contDiffOn_fromCart : ContDiffOn ℝ ∞ fromCart imgCart := by sorry
