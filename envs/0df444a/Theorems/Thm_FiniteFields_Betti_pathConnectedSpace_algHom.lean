-- Prove2me | Theorems.Thm_FiniteFields_Betti_pathConnectedSpace_algHom
-- name    : FiniteFields.Betti.pathConnectedSpace_algHom
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:40:38.142068+00:00
-- url     : https://prove2.me/theorems/2d36acaa-af69-41ba-89a2-40ddbe0840ce
-- title:
--   The complex points of an irreducible affine complex variety form a path-connected space
-- statement:
--   Let $A$ be a finitely generated $\mathbb C$-algebra which is an integral domain, so that $V=\operatorname{Spec}A$ is an irreducible affine variety over $\mathbb C$. Its complex points are the $\mathbb C$-algebra homomorphisms $\varphi:A\to\mathbb C$; give the set $V(\mathbb C)=\operatorname{Hom}_{\mathbb C\text{-alg}}(A,\mathbb C)$ the weakest topology making every evaluation $\varphi\mapsto\varphi(a)$, $a\in A$, continuous (the topology induced from the product $\mathbb C^A$). Then
--   $$V(\mathbb C)\ \text{ is path-connected.}$$
--
--   If $A=\mathbb C[x_1,\dots,x_m]/\mathfrak p$, this topology is the Euclidean topology of the zero set of $\mathfrak p$ in $\mathbb C^m$, so the statement is the classical fact that an irreducible complex affine variety is connected in the complex topology. It is the local input for the connectedness of $Y(\mathbb C)$ for geometrically irreducible schemes, i.e. $b_0=1$.
--
--   **Formalization Note** The topology is written explicitly as `TopologicalSpace.induced (fun φ ↦ ⇑φ)` from the product topology on `A → ℂ`; the statement uses only Mathlib.
-- source:
--   D. Mumford, *Algebraic Geometry I: Complex Projective Varieties*, Grundlehren 221, Springer 1976, Corollary (4.16), p. 68: for a projective variety X and a proper closed algebraic subset Y, X ∖ Y is connected in the classical topology (an irreducible affine variety is of this form, Y being the hyperplane at infinity); I. R. Shafarevich, *Basic Algebraic Geometry 2*, 3rd ed., Springer 2013, Chapter 7, “The Topology of Algebraic Varieties” (pp. 115–148): connectedness of X(ℂ) for an irreducible variety X. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Betti/Connected/` (`Core.lean`).

import Mathlib

theorem FiniteFields.Betti.pathConnectedSpace_algHom (A : Type) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    @PathConnectedSpace (A →ₐ[ℂ] ℂ)
      (TopologicalSpace.induced (fun φ : A →ₐ[ℂ] ℂ ↦ (⇑φ : A → ℂ)) inferInstance) := by sorry
