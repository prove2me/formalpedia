-- Prove2me | Theorems.Thm_FiniteFields_Betti_bettiNumber_zero_complexPoints
-- name    : FiniteFields.Betti.bettiNumber_zero_complexPoints
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:41:38.837122+00:00
-- url     : https://prove2.me/theorems/29c4da4c-0fdc-497d-814a-2e5871dd37ce
-- title:
--   $b_0(Y(\mathbb C))=1$ for $Y$ geometrically irreducible and locally of finite type
-- statement:
--   Let $R$ be a commutative ring, $\sigma:R\to\mathbb C$ a ring homomorphism and $\pi:Y\to\operatorname{Spec}R$ a scheme over $R$. Its **complex points** along $\sigma$ are the morphisms $x:\operatorname{Spec}\mathbb C\to Y$ with $\pi\circ x=\operatorname{Spec}\sigma$, i.e. the $\mathbb C$-points of the base change $Y\times_{R,\sigma}\mathbb C$; they form the space $Y(\mathbb C)$ with the analytic topology of `FiniteFields_BettiNumbers`.
--
--   Assume that $\pi$ is locally of finite type and geometrically irreducible. Then the zeroth rational Betti number of $Y(\mathbb C)$ is
--   $$b_0\bigl(Y(\mathbb C)\bigr)=\dim_{\mathbb Q}H_0\bigl(Y(\mathbb C);\mathbb Q\bigr)=1.$$
--
--   This is the degree-$0$ case of the Betti number part of the Weil conjectures ($\deg P_0=1$ for $P_0=1-T$).
--
--   **Formalization Note** $b_0$ is `bettiNumber 0`, i.e. `Module.finrank ℚ` of rational singular homology; here $H_0$ is indeed one-dimensional.
-- source:
--   A. Weil, *Numbers of solutions of equations in finite fields*, Bull. Amer. Math. Soc. 55 (1949), 497–508 (the conjectures are stated at the end of the paper); R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer 1977, Appendix C; I. R. Shafarevich, *Basic Algebraic Geometry 2*, 3rd ed., Springer 2013, Chapter 7, “The Topology of Algebraic Varieties” (pp. 115–148): connectedness of X(ℂ) for an irreducible variety X. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Betti/Connected/BettiZero.lean`.

import Mathlib
import Definitions.Def_FiniteFields_BettiNumbers

open AlgebraicGeometry CategoryTheory

theorem FiniteFields.Betti.bettiNumber_zero_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ)
    {Y : Scheme.{0}} (π : Y ⟶ Spec (.of R)) [LocallyOfFiniteType π] [GeometricallyIrreducible π] :
    bettiNumber 0 (ComplexPoints σ π) = 1 := by sorry
