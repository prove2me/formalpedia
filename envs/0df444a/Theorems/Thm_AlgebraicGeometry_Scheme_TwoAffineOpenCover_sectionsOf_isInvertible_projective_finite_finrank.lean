-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionsOf_isInvertible_projective_finite_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/74332d8e-79fe-56b1-a255-128199cd6df2
-- title:
--   Chart sections of an invertible sheaf: projective, finite, rank one
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal V$ a two-affine open cover of $X$, that is, a pair of opens $U_0, U_1 \subseteq X$ with $U_0$, $U_1$ and $U_0 \cap U_1$ affine and $U_0 \sqcup U_1 = \top$. Let $c \colon X \to \operatorname{Spec} R$ be a morphism, used to endow the three section rings with $R$-algebra structures, and let $M$ be a sheaf of modules on $X$ satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $X$ lies in an open $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$ for the rings of the associated two-chart Čech cover, and $M_0 = \Gamma(M, U_0)$, $M_1 = \Gamma(M, U_1)$, $M_{01} = \Gamma(M, U_0 \cap U_1)$ for the corresponding modules of sections. The conclusion is a ninefold conjunction: for each index $j \in \{0, 1, 01\}$, the module $M_j$ is projective over $A_j$, finite (finitely generated) over $A_j$, and for every field $K$ with an $A_j$-algebra structure one has $\dim_K(K \otimes_{A_j} M_j) = 1$.
--
--   This is the statement that an invertible sheaf restricted to each chart of a two-affine open cover, and to the overlap, has sections forming a finitely generated projective module of constant rank one over the chart ring. It packages the three chart-wise facts in the form used by the two-chart Čech description of the relative Picard functor, and is cited in the construction of rigidified line bundles over square-zero extensions and in the proof that the relative Picard presheaf has the required finiteness and injectivity properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionsOf_isInvertible_projective_finite_finrank
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Module.Projective (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    Module.Finite (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0) = 1) ∧
    Module.Projective (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    Module.Finite (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1) = 1) ∧
    Module.Projective (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    Module.Finite (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A01 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A01] (𝒱.sectionsOf c M).M01) = 1) := by sorry
