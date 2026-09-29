-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- name    : AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/c15ec286-3cfd-52c8-ba0a-3455fe7cf8f3
-- title:
--   Uniqueness of morphisms agreeing on all adic thickenings
-- statement:
--   Let $R$ be a Noetherian commutative ring and $I \subseteq R$ an ideal such that $R$ is $I$-adically complete, let $X$ and $Y$ be schemes, and let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms. Assume $X$ is projective over the base in the following sense: there is $N$ and a closed immersion $\iota_X$ of $X$ into $\operatorname{Proj}$ of the homogeneous subalgebra of $R[x_0,\dots,x_N]$ (i.e. projective $N$-space over $R$) whose composite with the structure morphism `ProjSpace.π R N` is $f$; likewise there is $N'$ and a closed immersion $\iota_Y$ of $Y$ into projective $N'$-space over $R$ whose composite with the structure morphism is $g$. Let $\psi, \psi' : X \to Y$ be two morphisms over the base, i.e. $\psi$ followed by $g$ and $\psi'$ followed by $g$ both equal $f$. For each $n$ write $X_n = \operatorname{adicThickening} f\, I\, n$ for the fibre product of $f$ with $\operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$, and let $\operatorname{adicThickening\iota} f\, I\, n : X_n \to X$ be its projection to $X$. If for every $n$ the composites of this projection with $\psi$ and with $\psi'$ agree, then $\psi = \psi'$.
--
--   This is the uniqueness half of Grothendieck's existence theorem for morphisms between projective schemes over an $I$-adically complete Noetherian base (EGA III, 5.4.1): a morphism over the base is determined by the compatible system of its restrictions to the thickenings $X \times_R \operatorname{Spec}(R/I^{n+1})$. It is used for the existence-and-uniqueness statement [`AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj) and, in the study of good reduction of Jacobians, for identifying a lift of a group law from its thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιY : IsClosedImmersion ιY)
    (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (ψ ψ' : X ⟶ Y) (hψ : ψ ≫ g = f) (hψ' : ψ' ≫ g = f)
    (h : ∀ n : ℕ, adicThickeningι f I n ≫ ψ = adicThickeningι f I n ≫ ψ') :
    ψ = ψ' := by sorry
