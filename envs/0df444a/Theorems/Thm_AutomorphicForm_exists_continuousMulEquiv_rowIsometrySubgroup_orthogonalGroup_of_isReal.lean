-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
-- name    : AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/2b13758f-8390-58a4-af9e-d9b8f3857daa
-- title:
--   Row isometries at a real place form O(2)
-- statement:
--   Let $F$ be a field, let $w$ be an infinite place of $F$, and assume $w$ is real. Write $F_w$ for the completion `w.Completion`, a normed field, and let `extensionEmbeddingOfIsReal hw` denote the isometric ring homomorphism $F_w \to \mathbb{R}$ attached to the real place $w$. Inside $\mathrm{GL}_2(F_w)$ consider the subgroup `rowIsometrySubgroup w.Completion` consisting of those $k$ whose underlying matrix satisfies $\lVert \det k\rVert = 1$ and $\lVert x k_{00} + y k_{10}\rVert^2 + \lVert x k_{01} + y k_{11}\rVert^2 = \lVert x\rVert^2 + \lVert y\rVert^2$ for all $x, y \in F_w$, i.e. right multiplication by $k$ preserves the quadratic norm of row vectors; it carries the subspace topology. The assertion is that there exists a continuous multiplicative equivalence $e$ (a group isomorphism which is simultaneously a homeomorphism, with continuous inverse) from this subgroup onto the orthogonal group `Matrix.orthogonalGroup (Fin 2) ℝ`, with the entrywise compatibility that for every $k$ in the subgroup and all $i, j \in \mathrm{Fin}\,2$, the $(i,j)$ entry of the real matrix underlying $e(k)$ is the image of $k_{ij}$ under `extensionEmbeddingOfIsReal hw`.
--
--   This identifies the archimedean local factor of the maximal compact subgroup of adelic $\mathrm{GL}_2$ at a real place with $\mathrm{O}(2)$, entry by entry and compatibly with topologies. It is used in the treatment of windowed Siegel-type conditions, namely in the polynomial description of functions with finite-dimensional span of right translates at a real place and in the compactness statement for the intersection of row-isometry subgroups over the infinite adeles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal.lean

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
    (F : Type) [Field F] (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
          = extensionEmbeddingOfIsReal hw
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by sorry
