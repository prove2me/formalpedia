-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Minkowski_R4_hasDerivAt_toCart
-- name    : ExactVacuumAtlas.Minkowski.R4.hasDerivAt_toCart
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:28:13.560804+00:00
-- url     : https://prove2.me/theorems/8120917f-f7e0-426b-b37b-016c8f500e15
-- title:
--   Jacobian of the spherical-to-Cartesian map, entrywise as genuine derivatives
-- statement:
--   Let $\Phi(t,r,\theta,\varphi)=(t,\ r\sin\theta\cos\varphi,\ r\sin\theta\sin\varphi,\ r\cos\theta)$ and $$J(x)=\begin{pmatrix}1&0&0&0\\0&\sin\theta\cos\varphi&r\cos\theta\cos\varphi&-r\sin\theta\sin\varphi\\0&\sin\theta\sin\varphi&r\cos\theta\sin\varphi&r\sin\theta\cos\varphi\\0&\cos\theta&-r\sin\theta&0\end{pmatrix}.$$ For every $x\in\mathbb R^4$ and all indices $k,i\in\{0,1,2,3\}$, the one-variable function $u\mapsto\Phi(x[x_i:=u])_k$ has derivative $J(x)_{ki}$ at $u=x_i$.
--
--   Jacobian obligation of relation R4, stated without any domain restriction; $\det J=r^2\sin\theta$.
--
--   **Formalization Note** Row $k$ is the output component, column $i$ the input coordinate; each entry is a `HasDerivAt` statement.
-- source:
--   elementary spherical coordinates on R^3 (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Minkowski/R4.lean#L330-L392 (module Atlas.Minkowski.R4, file sha256 a1fc97dfc0dd15a14ffbb8dfbee1cfe1421e5f3119a6b8607bb683d8caafc495; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_Minkowski_R4_hasDerivAt_toCart.lean)

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

theorem ExactVacuumAtlas.Minkowski.R4.hasDerivAt_toCart (x : Pt 4) (k i : Fin 4) :
    HasDerivAt (fun u => toCart (Function.update x i u) k) (jac x k i) (x i) := by sorry
