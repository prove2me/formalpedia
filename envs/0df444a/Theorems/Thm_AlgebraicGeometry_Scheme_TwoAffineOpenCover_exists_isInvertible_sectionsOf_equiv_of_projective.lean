-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/f606a213-8947-55ec-9609-12e5772e5160
-- title:
--   Invertible module glued from rank-one chart modules over a two-affine cover
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\mathcal V$ a two-chart affine open cover of $X$ (affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine), and $c:X\to\operatorname{Spec}R$ a morphism. Write $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$, regarded as $R$-algebras via $c$, with $\rho_0,\rho_1$ the restriction $R$-algebra maps into $A_{01}$; these data form `𝒱.cover c`. Let $P_0$ be a finite projective $A_0$-module and $P_1$ a finite projective $A_1$-module such that for every field $K$ of the ambient universe carrying an $A_0$-algebra (resp. $A_1$-algebra) structure one has $\dim_K(K\otimes_{A_0}P_0)=1$ (resp. $\dim_K(K\otimes_{A_1}P_1)=1$), and let $\sigma$ be an $A_{01}$-linear isomorphism $A_{01}\otimes_{A_0}P_0\xrightarrow{\sim}A_{01}\otimes_{A_1}P_1$, the two $A_{01}$-algebra structures being those given by $\rho_0$ and $\rho_1$. The assertion is that there exists a module $L$ on $X$ (an object of `X.Modules`) which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module on $U$, together with an $A_0$-linear isomorphism $e_0:\Gamma(L,U_0)\xrightarrow{\sim}P_0$, an $A_1$-linear isomorphism $e_1:\Gamma(L,U_1)\xrightarrow{\sim}P_1$ and an $A_{01}$-linear isomorphism $e_{01}:\Gamma(L,U_0\cap U_1)\xrightarrow{\sim}A_{01}\otimes_{A_0}P_0$ such that $e_{01}(m|_{U_0\cap U_1})=1\otimes e_0(m)$ for all $m\in\Gamma(L,U_0)$ and $\sigma\bigl(e_{01}(m|_{U_0\cap U_1})\bigr)=1\otimes e_1(m)$ for all $m\in\Gamma(L,U_1)$.
--
--   This is the gluing (descent) statement for an invertible module along a Zariski cover by two affine charts, with no cocycle condition to impose since there is a single overlap; it is the converse, at rank one, to the passage from a module on $X$ to its triple of chart sections $\Gamma(L,U_0),\Gamma(L,U_1),\Gamma(L,U_0\cap U_1)$ recorded by `𝒱.sectionsOf`. It is used in the construction of line bundles on relative curves from explicit chart data, in particular in the analysis of rigidified line bundles over square-zero extensions and of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (P0 : Type u) [AddCommGroup P0] [Module (𝒱.cover c).A0 P0]
    [Module.Projective (𝒱.cover c).A0 P0] [Module.Finite (𝒱.cover c).A0 P0]
    (P1 : Type u) [AddCommGroup P1] [Module (𝒱.cover c).A1 P1]
    [Module.Projective (𝒱.cover c).A1 P1] [Module.Finite (𝒱.cover c).A1 P1]
    (hrk0 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] P0) = 1)
    (hrk1 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] P1) = 1)
    (σ : letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
         letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
         ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0) ≃ₗ[(𝒱.cover c).A01]
           ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] P1)) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] P0)
        (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] P1)
        (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01]
          ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0)),
        (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] e0 m) ∧
        (∀ m, σ (e01 ((𝒱.sectionsOf c L).r1 m)) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] e1 m) := by sorry
