-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_R4_toCart_fromCart
-- name    : ExactVacuumAtlas.Minkowski.R4.toCart_fromCart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:29:22.780539+00:00
-- url     : https://prove2.me/theorems/ec278d9c-122a-4dbf-b46c-b04b38edc2ee
-- title:
--   Spherical chart: the inverse map is inverted on the slit image
-- statement:
--   Let $\Phi$ be the spherical-to-Cartesian map and $\Psi$ its inverse of bundle `Atlas_Minkowski_R4`. For every $y=(t,x,y,z)$ in $V=\{\neg(y=0\wedge x\ge0)\}$ (the complement of the closed half-plane $\{y=0,x\ge0\}$), $$\Phi(\Psi(y))=y.$$
--
--   Right-inverse obligation of relation R4. Together with the domain-mapping results ($\Phi$ maps the chart into $V$, $\Psi$ maps $V$ into the chart) and the left-inverse identity, the two round-trip identities establish the stated bijection between the chart domain and its image $V$ (the `BijOn` field of the R4 coordinate relation).
-- source:
--   elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/R4.lean#L212-L270 (module Atlas.Minkowski.R4, file sha256 a1fc97dfc0dd15a14ffbb8dfbee1cfe1421e5f3119a6b8607bb683d8caafc495; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_R4_toCart_fromCart.lean)

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

theorem ExactVacuumAtlas.Minkowski.R4.toCart_fromCart {y : Pt 4} (hy : y ∈ imgCart) : toCart (fromCart y) = y := by sorry
