-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/35eb19fc-b736-5051-a64b-339dc24ca1f8
-- title:
--   Finite surjection onto a normal curve-like base is flat of constant generic rank
-- statement:
--   Let $\pi\colon X\to Y$ be a morphism of schemes which is finite and surjective, with $X$ and $Y$ integral and $Y$ locally Noetherian, and assume that for every point $y$ of $Y$ the local ring $\mathcal O_{Y,y}$ (the stalk of the structure presheaf) is integrally closed and has Krull dimension at most $1$. Let $U$ be an open subscheme of $Y$ which is affine and whose underlying space is non-empty, and let $d$ be a natural number. Give $\Gamma(X,\pi^{-1}U)$ the $\Gamma(Y,U)$-algebra structure coming from the ring map $\pi^{\sharp}$ associated with $U$ and its preimage (`π.appLE U (π ⁻¹ᵁ U) le_rfl`), and assume that the base change of this algebra to the function field of $Y$ has finite rank exactly $d$, i.e. $\dim_{K(Y)}\bigl(K(Y)\otimes_{\Gamma(Y,U)}\Gamma(X,\pi^{-1}U)\bigr)=d$. The conclusion asserts, in the form of an existential over a witness that $\pi$ is locally of finite presentation, that $\pi$ is locally of finite presentation, that $\pi$ is flat, and that for every point $y$ of $Y$ the rank `π.finrank y` of $\pi$ at $y$ equals $d$.
--
--   This is the statement that a finite surjective morphism from an integral scheme onto an integral, locally Noetherian scheme all of whose local rings are normal of dimension at most $1$ is finite locally free of constant rank, the rank being read off from the generic fibre on a single affine chart. The chart form of the rank hypothesis makes it usable for explicit two-chart models of curves: it is cited in the construction of curve models and in the computation of degrees of degeneracy and Hecke maps between modular curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdim : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1)

    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (d : ℕ)
    (hd : letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      Module.finrank Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) = d) :
    ∃ (_ : LocallyOfFinitePresentation π), Flat π ∧ ∀ y : Y, π.finrank y = d := by sorry
