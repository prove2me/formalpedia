-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
-- name    : AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9a0429fc-96b7-544e-97bf-ef3452334963
-- title:
--   Separating transcendental element when dim_F Ω_{F/K} = 1
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra which is essentially of finite type over $K$ (so $F$ is generated over $K$ by finitely many elements together with localisation, i.e. finitely generated as a field extension) and which is transcendental over $K$, meaning that $F$ is not algebraic over $K$. Assume that the module of Kähler differentials $\Omega_{F/K}$, viewed as an $F$-vector space, has rank exactly one, $\operatorname{finrank}_F \Omega_{F/K} = 1$. The conclusion is the existence of an element $t \in F$ with three properties: $t$ is transcendental over $K$; $F$ is finite-dimensional as a vector space over the intermediate field $K\langle t\rangle = K(t)$ obtained by adjoining $t$ to $K$ inside $F$; and the extension $F/K(t)$ is separable, in the sense that every element of $F$ has separable minimal polynomial over $K(t)$. Thus $t$ is a separating transcendental element: $F$ is a finite separable extension of the rational function field $K(t)$.
--
--   This is the replacement, over an arbitrary base field $K$, of the classical statement that a finitely generated extension of transcendence degree one of a perfect field admits a separating transcendence basis; perfectness is traded for the intrinsic hypothesis $\dim_F \Omega_{F/K} = 1$. It serves as the basic structural input for the function-field theory of curves in this development, and is invoked wherever a one-dimensional space of differentials must be converted into a finite separable presentation $F/K(t)$, for instance in the treatment of places, of Riemann–Roch spaces and of torsion in degree-zero Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one.lean

import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IntermediateField

theorem AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [Algebra.EssFiniteType K F]
    [Algebra.Transcendental K F] (hΩ : Module.finrank F Ω[F⁄K] = 1) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by sorry
