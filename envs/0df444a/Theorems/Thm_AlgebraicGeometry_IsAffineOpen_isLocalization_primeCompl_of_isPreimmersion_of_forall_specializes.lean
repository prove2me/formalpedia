-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
-- name    : AlgebraicGeometry.IsAffineOpen.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/ab57c0cc-56c8-5002-a3c6-f391be1dbd00
-- title:
--   Localisation at a maximal point of a reduced scheme
-- statement:
--   Let $X$ be a reduced scheme and $V \subseteq X$ an open subset which is affine (witnessed by `hV`), and let $x$ be a point of $X$ lying in $V$ such that every $y \in X$ with $y \rightsquigarrow x$ satisfies $y = x$; that is, $x$ admits no proper specialisation onto itself, so $x$ is maximal for the specialisation order. Let $F$ be a field (in the same universe as $X$) and let $\varphi \colon \operatorname{Spec} F \to X$ be a morphism of schemes which is a preimmersion, i.e. its underlying map is a topological embedding and it is surjective on stalks, and assume that $\varphi$ sends the closed point of $\operatorname{Spec} F$ to $x$. Assume further that $F$ is given an algebra structure over the ring of sections $\Gamma(X, V)$ such that $\varphi$ factors as $\operatorname{Spec}$ of the structure map $\Gamma(X,V) \to F$ followed by the canonical morphism $\operatorname{Spec} \Gamma(X,V) \to X$ attached to the affine open $V$. Writing $\mathfrak p_x \subseteq \Gamma(X,V)$ for the prime ideal corresponding to $x$ under the identification of $V$ with $\operatorname{Spec}\Gamma(X,V)$, the conclusion is that the structure map exhibits $F$ as the localisation of $\Gamma(X,V)$ at the multiplicative set $\Gamma(X,V) \setminus \mathfrak p_x$, i.e. $F \cong \Gamma(X,V)_{\mathfrak p_x}$ compatibly with $\Gamma(X,V) \to F$.
--
--   This is the scheme-theoretic statement that at a generic point of a reduced scheme the local ring coincides with the residue field, so that any field-valued point with embedding-type (preimmersion) structure at such a point realises the field as the localisation of the coordinate ring of an affine neighbourhood. It is used in the construction of component-reading data for smooth schemes, in [`NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes`](thm.html#NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineOpen.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
    {X : Scheme.{u}} [IsReduced X] {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hxV : x ∈ V) (hmax : ∀ y : X, y ⤳ x → y = x)
    (F : Type u) [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
    (hφx : φ.base (IsLocalRing.closedPoint F) = x)
    [Algebra Γ(X, V) F]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec = φ) :
    IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl F := by sorry
