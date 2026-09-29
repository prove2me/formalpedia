-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat
-- name    : AlgebraicGeometry.ProjSpace.flat_cochain_twist_and_subsingleton_cochain_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7ae4c116-d50c-5f6d-a3cc-6f957e91e0d3
-- title:
--   Flatness and vanishing of Čech cochains of mathcal O_Z(d)
-- statement:
--   Let $A$ be a commutative ring, $n$ a natural number, $Z$ a scheme, and $\iota : Z \to \operatorname{Proj}$ of the graded ring $\bigoplus_k (\text{homogeneous polynomials of degree } k)$ in $\mathrm{Fin}(n+1)$ variables over $A$ — that is, $Z \to \mathbb P^n_A$ — a closed immersion, and assume the composite $\iota$ followed by the structure morphism $\pi : \mathbb P^n_A \to \operatorname{Spec} A$ is flat; let $d$ be a natural number. Consider the ordered affine cover `ProjSpace.stdCoverPullback` of $Z$ indexed by $\mathrm{Fin}(n+1)$ (up to a universe lift), whose $j$-th member is the $\iota$-preimage of the basic open $D_+(x_j)$, and the presheaf of $A$-modules `ProjSpace.twist` of the $d$-th twist for $\iota$ over $\pi \circ \iota$, whose sections on an open $U$ are families $(g_i)_{i}$ with $g_i \in \Gamma(Z, U \cap \iota^{-1}D_+(x_i))$ satisfying the compatibility predicate `TwistCompat` in degree $d$. The assertion is twofold: first, for every $i$ the $i$-th cochain module, namely the product of the twist sections over the intersections $\bigcap_{t} U_{s(t)}$ taken over all strictly increasing $(i+1)$-tuples $s$ of chart indices, is a flat $A$-module; second, for every $i \ge n+1$ that cochain module is a subsingleton.
--
--   This is the basic finiteness and flatness input for computing the cohomology of $\mathcal O_Z(d)$ on a flat closed subscheme $Z \subseteq \mathbb P^n_A$ by the alternating Čech complex of the pulled-back standard cover: the complex consists of flat $A$-modules and is concentrated in degrees $\le n$. It is used in the construction of points of the Hilbert functor, in [`AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.flat_cochain_twist_and_subsingleton_cochain_of_flat
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (hfl : Flat (ι ≫ ProjSpace.π A n)) (d : ℕ) :
    (∀ i : ℕ, Module.Flat A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)) ∧
    (∀ i : ℕ, n + 1 ≤ i →
      Subsingleton ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)) := by sorry
