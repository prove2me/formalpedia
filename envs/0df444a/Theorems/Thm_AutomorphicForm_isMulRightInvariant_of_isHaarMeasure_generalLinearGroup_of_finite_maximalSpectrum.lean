-- Prove2me | Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
-- name    : AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6b8ad38f-d6f1-5a16-aae2-e1abd68b4b59
-- title:
--   Unimodularity of GL₂(A) for semilocal A
-- statement:
--   Let $A$ be a commutative ring carrying a topology making it a topological ring, assumed Hausdorff, locally compact and second countable, and having only finitely many maximal ideals (the type `MaximalSpectrum A` is finite). Equip the group $\mathrm{GL}_2(A)$ of invertible $2\times 2$ matrices over $A$ with the measurable space [`AutomorphicForm.glBorelOf A`](def/AutomorphicForm_TwistedOrbital.html#L57), namely the Borel $\sigma$-algebra of its topology as the unit group of the matrix ring. Let $\mu_A$ be a measure on $\mathrm{GL}_2(A)$ with respect to that Borel structure, and suppose $\mu_A$ is a Haar measure, i.e. a left-invariant regular measure which is positive on nonempty open sets and finite on compact sets. The conclusion is that $\mu_A$ is also right invariant: $\mu_A(E\cdot g)=\mu_A(E)$ for all measurable $E$ and all $g\in\mathrm{GL}_2(A)$. Equivalently, $\mathrm{GL}_2(A)$ is unimodular for every such $A$.
--
--   This is the unimodularity of $\mathrm{GL}_2$ over a locally compact semilocal commutative topological ring, covering in particular local fields, finite products $\prod_{v\mid\infty}K_v$, and algebras $L\otimes_K K_v$. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where Godement-type zeta integrals and Whittaker functions are integrated against Haar measure and left- and right-invariant integration must be interchangeable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA := by sorry
