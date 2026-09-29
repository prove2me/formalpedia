-- Prove2me | Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
-- name    : AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/87adeb97-58a2-5808-9fc2-3365e81816a9
-- title:
--   Codimension plus dimension of a closure on an integral k-scheme
-- statement:
--   Let $k$ be a field and let $X$ be a scheme equipped with a morphism $f \colon X \to \operatorname{Spec} k$ which is locally of finite type, and assume $X$ is integral (irreducible and reduced). Let $x$ be a point of $X$. Then, as an identity in $\mathbb{Z}\cup\{\pm\infty\}$ (the value type `WithBot ℕ∞` of both dimension functions),
--   $$\operatorname{ringKrullDim}\big(\mathcal{O}_{X,x}\big) + \operatorname{topologicalKrullDim}\big(\overline{\{x\}}\big) = \operatorname{topologicalKrullDim}(X),$$
--   where the first summand is the Krull dimension of the stalk of the structure sheaf of $X$ at $x$, the second is the topological Krull dimension (the supremum of lengths of chains of irreducible closed subsets) of the closure of $\{x\}$ in $X$ regarded as a topological space with the subspace topology, and the right-hand side is the topological Krull dimension of $X$. No finiteness of type over $k$ beyond local finiteness is assumed, and no separatedness or quasi-compactness hypothesis is imposed; the morphism $f$ enters only through the hypothesis that it is locally of finite type.
--
--   This is the biequidimensionality of irreducible varieties in the form most often used: the codimension of the irreducible closed subset $\overline{\{x\}}$, computed as the dimension of the local ring at its generic point $x$, and its dimension add up to the dimension of $X$. It is invoked in the construction of valuation subrings of the function field attached to points whose local ring has dimension one, and in the analysis of partial actions on stable loci in the study of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X := by sorry
