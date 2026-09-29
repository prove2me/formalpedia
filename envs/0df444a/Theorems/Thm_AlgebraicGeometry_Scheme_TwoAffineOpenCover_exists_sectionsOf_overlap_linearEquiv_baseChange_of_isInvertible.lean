-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f76df78c-d944-5442-b9de-08894bfb9092
-- title:
--   Sections over the overlap as a base change (invertible case)
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal V$ a two-affine open cover of $X$, that is, a pair of opens $U_0, U_1 \subseteq X$ with $U_0$, $U_1$ and $U_0 \cap U_1$ affine and $U_0 \cup U_1 = X$; let $c \colon X \to \operatorname{Spec} R$ be a morphism, and let $M$ be a sheaf of modules over the structure sheaf of $X$ which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$ for the chart rings of the associated two-chart Čech cover, with $\rho_0, \rho_1 \colon A_j \to A_{01}$ the restriction $R$-algebra maps, and $M_0 = \Gamma(M, U_0)$, $M_1 = \Gamma(M, U_1)$, $M_{01} = \Gamma(M, U_0 \cap U_1)$ with $r_0, r_1$ the restriction maps, $R$-linear and semilinear over $\rho_0$, $\rho_1$. Regarding $A_{01}$ as an $A_0$-algebra via $\rho_0$ and as an $A_1$-algebra via $\rho_1$, the assertion is that there exist $A_{01}$-linear isomorphisms $A_{01} \otimes_{A_0} M_0 \cong M_{01}$ and $A_{01} \otimes_{A_1} M_1 \cong M_{01}$ sending $1 \otimes m$ to $r_0(m)$, respectively to $r_1(m)$. Only existence is asserted, not uniqueness of such isomorphisms.
--
--   This is the statement that the sections of an invertible sheaf over the affine overlap of the two charts are obtained from the sections over either chart by base change along the restriction map of chart rings, i.e. the standard localisation description of sections of a quasi-coherent sheaf on an affine scheme. It is the step that makes the transition-function description of an invertible sheaf on a two-chart cover available, and it is used in the comparison of two-chart sections data with sheaves (including `nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible`) and in the finiteness statements for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (rbc0 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01)
      (rbc1 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01),
      (∀ m, rbc0 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] m) = (𝒱.sectionsOf c M).r0 m) ∧
      (∀ m, rbc1 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] m) = (𝒱.sectionsOf c M).r1 m) := by sorry
