-- Prove2me | Theorems.Thm_FiniteFields_Betti_complexPoints_pathConnected
-- name    : FiniteFields.Betti.complexPoints_pathConnected
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:41:15.47606+00:00
-- url     : https://prove2.me/theorems/96a317f7-a63a-44aa-8a85-d560abbf3b2f
-- title:
--   $Y(\mathbb C)$ is path-connected when $Y$ is geometrically irreducible and locally of finite type
-- statement:
--   Let $R$ be a commutative ring, $\sigma:R\to\mathbb C$ a ring homomorphism and $\pi:Y\to\operatorname{Spec}R$ a scheme over $R$. Its **complex points** along $\sigma$ are the morphisms $x:\operatorname{Spec}\mathbb C\to Y$ with $\pi\circ x=\operatorname{Spec}\sigma$, i.e. the $\mathbb C$-points of the base change $Y\times_{R,\sigma}\mathbb C$; they form the space $Y(\mathbb C)$ with the analytic topology of `FiniteFields_BettiNumbers`.
--
--   Assume that $\pi$ is locally of finite type and geometrically irreducible. Then
--   $$Y(\mathbb C)\ \text{ is path-connected.}$$
--
--   Only the fibre over $\operatorname{Spec}\sigma$ matters: the hypothesis implies that $Y\times_{R,\sigma}\mathbb C$ is irreducible, and its complex points form $Y(\mathbb C)$. In particular a geometrically irreducible variety over a number field or over a finite-type base has connected complex points, the topological counterpart of $b_0=1$.
--
--   **Formalization Note** "Geometrically irreducible" is Mathlib's `GeometricallyIrreducible π`: every base change along a field is irreducible. Path-connectedness includes non-emptiness.
-- source:
--   I. R. Shafarevich, *Basic Algebraic Geometry 2*, 3rd ed., Springer 2013, Chapter 7, “The Topology of Algebraic Varieties” (pp. 115–148): connectedness of X(ℂ) for an irreducible variety X; D. Mumford, *Algebraic Geometry I: Complex Projective Varieties*, Grundlehren 221, Springer 1976, Corollary (4.16), p. 68: for a projective variety X and a proper closed algebraic subset Y, X ∖ Y is connected in the classical topology (an irreducible affine variety is of this form, Y being the hyperplane at infinity). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Betti/Connected/` (`Global.lean`, `Final.lean`).

import Mathlib
import Definitions.Def_FiniteFields_BettiNumbers

open AlgebraicGeometry CategoryTheory

theorem FiniteFields.Betti.complexPoints_pathConnected {R : Type} [CommRing R] (σ : R →+* ℂ)
    {Y : Scheme.{0}} (π : Y ⟶ Spec (.of R)) [LocallyOfFiniteType π] [GeometricallyIrreducible π] :
    PathConnectedSpace (ComplexPoints σ π) := by sorry
