-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- name    : AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/eb0ea1a4-babc-5be4-bf53-d5f0fe68005d
-- title:
--   Algebraisation of compatible morphisms between adic thickenings
-- statement:
--   Let $R$ be a Noetherian commutative ring and $I \subseteq R$ an ideal for which $R$ is $I$-adically complete, and let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms of schemes. Assume $X$ admits a closed immersion $\iota_X$ into $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$, i.e. $\mathbb P^N_R$, with $\iota_X$ followed by the structure morphism `ProjSpace.π R N` equal to $f$, and likewise $Y$ admits a closed immersion $\iota_Y$ into $\mathbb P^{N'}_R$ with $\iota_Y$ followed by `ProjSpace.π R N'` equal to $g$. For each $n$ put $X_n = X \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ and $Y_n = Y \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ (`adicThickening`), with the projections `adicThickeningι` to $X$, resp. $Y$, and `adicThickeningToBase` to $\operatorname{Spec}(R/I^{n+1})$, and with the transition morphisms $X_n \to X_{n+1}$, $Y_n \to Y_{n+1}$ (`adicThickeningTransition`). Given morphisms $\varphi_n : X_n \to Y_n$ such that $\varphi_n$ followed by the base projection of $Y_n$ equals that of $X_n$ (so $\varphi_n$ is a morphism over $R/I^{n+1}$), and such that the transition $X_n \to X_{n+1}$ followed by $\varphi_{n+1}$ equals $\varphi_n$ followed by the transition $Y_n \to Y_{n+1}$, the conclusion is that there is exactly one morphism $\psi : X \to Y$ with $\psi$ followed by $g$ equal to $f$ and with $X_n \hookrightarrow X \xrightarrow{\psi} Y$ equal to $X_n \xrightarrow{\varphi_n} Y_n \hookrightarrow Y$ for every $n$.
--
--   This is the bijectivity of $\operatorname{Hom}_R(X,Y) \to \varprojlim_n \operatorname{Hom}_{R/I^{n+1}}(X_n,Y_n)$ in the form of EGA III₁ 5.4.1, here with both $X$ and $Y$ assumed projective over $R$ via given closed immersions into projective spaces rather than $X$ proper and $Y$ separated of finite type. It is used to algebraise the multiplication and inversion morphisms of a group law given level by level on adic thickenings, in the construction of group structures on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιY : IsClosedImmersion ιY)
    (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by sorry
