-- Prove2me | Theorems.Thm_ConsistentSubmodular_TriangularArray_atomic_residual
-- name    : ConsistentSubmodular.TriangularArray.atomic_residual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:44.365188+00:00
-- url     : https://prove2.me/theorems/e355d12c-7efc-4a2f-8925-f2ad999a8baf
-- title:
--   Residuals of the atomic profile of a triangular array
-- statement:
--   Let $M$ be a triangular array with stages $0,\dots,m$: nonnegative lengths $\ell(i,j)$ with $\ell(i,j)=0$ for $j<i$, $\sum_j\ell(0,j)=1$, and $\sum_{j\ge t}\ell(i,j)\le\sum_{j\ge t}\ell(t,j)$ for all $i,t$. Let $\mathrm{toAtomic}(M)$ be its associated atomic profile, obtained by decomposing each column $j$ into the atoms of a maximum coverage with pool $j$. Then for all stages $i,t\in\{0,\dots,m\}$ the residual of this profile is
--   $$R(i,t)\;=\;\sum_{j=0}^{m}\mathbf 1[t\le j]\;\ell(i,j)\;=\;\sum_{j\ge t}\ell(i,j).$$
--
--   The identity says that the residual of the atomic profile is exactly the tail row sum of the array, which allows triangular arrays to be completed into atomic profiles in the certificate construction (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ArrayCompletion.lean#L83-L95 (`ConsistentSubmodular.TriangularArray.atomic_residual`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ArrayCompletion

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.TriangularArray
variable {m : ℕ} (M : TriangularArray m)

theorem ConsistentSubmodular.TriangularArray.atomic_residual (i t : Fin (m + 1)) :
    M.toAtomic.residual i t = ∑ j, if t ≤ j then M.length i j else 0 := by sorry
