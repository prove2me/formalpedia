-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion
-- name    : AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/555b00a2-1324-5017-9313-0fd963120c6b
-- title:
--   Closed subschemes of Pⁿ_k have dimension at most n
-- statement:
--   Let $k$ be a field (in a fixed universe), $n$ a natural number, and let $\mathcal{A}$ denote the graded $k$-algebra $\bigoplus_d \mathcal{A}_d$ given by the homogeneous submodules `MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k` of the polynomial ring in the $n+1$ variables indexed by `Fin (n + 1)`, so that $\operatorname{Proj} \mathcal{A}$ is projective $n$-space over $k$ as a scheme. Let $Z$ be a scheme and let $\iota : Z \to \operatorname{Proj} \mathcal{A}$ be a morphism of schemes which is a closed immersion. The conclusion is that the topological Krull dimension of the underlying topological space of $Z$ — the supremum of lengths of chains of irreducible closed subsets, taken in `WithBot ℕ∞` — is at most $n$. In particular no finiteness or reducedness hypothesis on $Z$ is imposed, and the bound is stated for the topological invariant of the underlying space rather than for a ring-theoretic dimension.
--
--   This is the standard bound $\dim Z \le n$ for a closed subscheme $Z$ of projective $n$-space over a field, together with the computation $\dim \mathbb{P}^n_k = n$ that underlies it. It is used to bound the degree of the Hilbert-type polynomial produced in the Snapper/Euler-characteristic argument, being cited by [`AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq`](thm.html#AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    topologicalKrullDim Z ≤ n := by sorry
