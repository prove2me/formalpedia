-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
-- name    : AutomorphicForm.continuous_unipotentGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/94ee6a20-1316-5251-abcc-05eff7224a21
-- title:
--   Continuity of the unipotent embedding into GL₂(R)
-- statement:
--   Let $R$ be a commutative ring carrying a topology for which negation $x \mapsto -x$ is continuous. The map [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17) sends $x \in R$ to the element of the unit group $\mathrm{GL}(\mathrm{Fin}\ 2, R)$ whose underlying matrix is $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ and whose designated inverse is $\begin{pmatrix} 1 & -x \\ 0 & 1\end{pmatrix}$, the two products in either order being the identity matrix. The assertion is that this map $R \to \mathrm{GL}(\mathrm{Fin}\ 2, R)$ is continuous, where the source has the given topology on $R$, the matrix algebra $M_2(R)$ has the product topology entrywise, and the unit group carries the topology of the group of units, namely the topology making both $g \mapsto g$ and $g \mapsto g^{-1}$ continuous into $M_2(R)$. No further hypothesis on $R$ is imposed: continuity of addition or multiplication on $R$ is not assumed, only continuity of negation.
--
--   This records that the upper-triangular unipotent one-parameter subgroup of $\mathrm{GL}_2$ is a continuous (indeed topological) embedding of the additive group of $R$, the intended case being $R$ an adele ring. It is used throughout the treatment of constant terms and cuspidality conditions for automorphic forms on $\mathrm{GL}_2$, where unipotent translates must vary continuously.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_unipotentGL2.lean

import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by sorry
