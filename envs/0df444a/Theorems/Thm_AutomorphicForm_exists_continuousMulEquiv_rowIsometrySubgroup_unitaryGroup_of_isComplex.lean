-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
-- name    : AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/76722388-bc0c-5b8e-b26d-c9491157d6a6
-- title:
--   Row isometries of GL₂(F_w) at a complex place form U(2)
-- statement:
--   Let $F$ be a field, let $w$ be an infinite place of $F$, and assume $w$ is complex. Write $F_w$ for the completion of $F$ at $w$, a normed field, and let $\iota_w \colon F_w \to \mathbb C$ denote the canonical ring homomorphism `extensionEmbedding w` extending the embedding attached to $w$. Inside $\mathrm{GL}_2(F_w)$ consider the subgroup `rowIsometrySubgroup` of those invertible matrices $k$ satisfying the two conditions $\lVert \det k\rVert = 1$ and, for all $x, y \in F_w$, $\lVert x k_{00} + y k_{10}\rVert^2 + \lVert x k_{01} + y k_{11}\rVert^2 = \lVert x\rVert^2 + \lVert y\rVert^2$ — that is, right multiplication by $k$ preserves the quadratic norm of row vectors — with the subspace topology. The assertion is that there exists a continuous multiplicative equivalence $e$ (a group isomorphism which is simultaneously a homeomorphism) from this subgroup onto the unitary group $\mathrm U(2) =$ `Matrix.unitaryGroup (Fin 2) ℂ` of $2 \times 2$ complex matrices, such that for every row isometry $k$ and all indices $i, j \in \{0,1\}$ the $(i,j)$ entry of the matrix $e(k)$ equals $\iota_w(k_{ij})$. Thus the isomorphism is entrywise given by the completion's embedding into $\mathbb C$, not merely abstract.
--
--   This identifies the archimedean row-isometry subgroup at a complex place with the standard maximal compact subgroup $\mathrm U(2)$ of $\mathrm{GL}_2(\mathbb C)$, entry by entry and compatibly with group structures and topologies. It is used in the analysis of automorphic forms at the archimedean places: in the compactness statement for the intersection of row-isometry subgroups inside $\mathrm{GL}_2$ of the infinite adele ring, and in the polynomial description of functions with finite-dimensional span of right translates at a complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex.lean

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
    (F : Type) [Field F] (w : InfinitePlace F) (_hw : w.IsComplex) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.unitaryGroup (Fin 2) ℂ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j
          = extensionEmbedding w
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by sorry
