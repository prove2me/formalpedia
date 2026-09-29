-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
-- name    : AlgebraicGeometry.exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ddadce78-e5e9-5136-8b27-237d0c1ce7ea
-- title:
--   Algebraisation of morphisms between projective schemes over a complete ring
-- statement:
--   Let $R$ be a noetherian commutative ring and $I \subseteq R$ an ideal for which $R$ is $I$-adically complete. Let $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$ be morphisms of schemes, and suppose each factors through a projective space in the following sense: there are $r_X, r_Y \in \mathbb{N}$ and finite morphisms $G_X : X \to \operatorname{Proj}$ of the graded ring $\bigoplus_d$ (homogeneous polynomials of degree $d$ in $r_X + 1$ variables over $R$), resp. $G_Y$ into the analogous $\operatorname{Proj}$ for $r_Y + 1$ variables, such that $G_X$ followed by the structure morphism `ProjSpace.π R rX` is $f$, and likewise for $G_Y$ and $g$. Let $sR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec} R$ be the morphisms induced by the quotient maps, and let $tR_n : \operatorname{Spec}(R/I^{n+1}) \to \operatorname{Spec}(R/I^{n+2})$ satisfy $sR_{n+1} \circ tR_n = sR_n$. Write $X_n$ for the chosen pullback of $f$ along $sR_n$ and $Y_n$ for that of $g$, and let $x_n : X_n \to X_{n+1}$, $y_n : Y_n \to Y_{n+1}$ be transition morphisms commuting with the first projections and compatible with $tR_n$ on the second. Given morphisms $\varphi_n : X_n \to Y_n$ over $\operatorname{Spec}(R/I^{n+1})$ (i.e. the second projection of $Y_n$ composed after $\varphi_n$ is that of $X_n$) with $\varphi_{n+1} \circ x_n = y_n \circ \varphi_n$, the conclusion asserts the existence of $F : X \to Y$ with $g \circ F = f$ and $F \circ \mathrm{pr}_1^{X_n} = \mathrm{pr}_1^{Y_n} \circ \varphi_n$ for all $n$, and that any $F'$ over $\operatorname{Spec} R$ with the same compatibilities equals $F$.
--
--   This is Grothendieck's algebraisation of morphisms (EGA III 5.4.1) in the projective case: $\operatorname{Hom}_R(X,Y) \to \varprojlim_n \operatorname{Hom}_{R/I^{n+1}}(X_n, Y_n)$ is bijective when $X$ is finite over a projective space over the complete ring $R$ and so is $Y$. It is phrased with explicit chosen pullbacks and pinned transition morphisms, and is used in the construction of the Čerednik–Drinfeld fake elliptic curves to algebraise compatible systems of automorphisms, multiplication maps and sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (rX : ℕ) (GX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rX + 1)) R)) [IsFinite GX] (hGX : GX ≫ ProjSpace.π R rX = f)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of R))
    (rY : ℕ) (GY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rY + 1)) R)) [IsFinite GY] (hGY : GY ≫ ProjSpace.π R rY = g)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)
    (yn : ∀ n : ℕ, Limits.pullback g (sR n) ⟶ Limits.pullback g (sR (n + 1)))
    (hyn₁ : ∀ n : ℕ, yn n ≫ Limits.pullback.fst g (sR (n + 1)) = Limits.pullback.fst g (sR n))
    (hyn₂ : ∀ n : ℕ, yn n ≫ Limits.pullback.snd g (sR (n + 1)) = Limits.pullback.snd g (sR n) ≫ tR n)

    (φ : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback g (sR n))
    (hφ : ∀ n : ℕ, φ n ≫ Limits.pullback.snd g (sR n) = Limits.pullback.snd f (sR n))
    (hφc : ∀ n : ℕ, xn n ≫ φ (n + 1) = φ n ≫ yn n) :
    ∃ F : X ⟶ Y, F ≫ g = f ∧
      (∀ n : ℕ, Limits.pullback.fst f (sR n) ≫ F = φ n ≫ Limits.pullback.fst g (sR n)) ∧
      ∀ F' : X ⟶ Y, F' ≫ g = f →
        (∀ n : ℕ, Limits.pullback.fst f (sR n) ≫ F' = φ n ≫ Limits.pullback.fst g (sR n)) → F' = F := by sorry
