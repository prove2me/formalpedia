-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1f84dd8f-6e38-5d03-a9e6-d9a63446d4a2
-- title:
--   Two-chart Čech cohomology under base change
-- statement:
--   Let $R$ be a commutative ring and $X$ a scheme equipped with a `TwoAffineOpenCover` $\mathcal V$, that is, two opens $U_0, U_1 \subseteq X$, both affine, with affine intersection $U_0 \cap U_1$ and $U_0 \sqcup U_1 = \top$; let $c : X \to \operatorname{Spec} R$ be a morphism and $M$ a sheaf of modules on $X$. Assume $M$ is Zariski-locally trivial in the sense that every point of $X$ lies in some open $V$ for which the pullback of $M$ along the inclusion $V \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $V$. Let $A$ be an $R$-algebra. Form $X_A$ as the fibre product of $c$ and $\operatorname{Spec}$ of the structure map $R \to A$, with the cover $\mathcal V$ pulled back along the first projection, the structure morphism to $\operatorname{Spec} A$ given by the second projection, and $M_A$ the pullback of $M$ along the first projection. Writing, for a two-chart cover, $d$ for the Čech differential $(m_0,m_1) \mapsto m_1|_{U_0 \cap U_1} - m_0|_{U_0 \cap U_1}$ on $\Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M, U_0 \cap U_1)$, with $H^0 = \ker d$ and $H^1 = \operatorname{coker} d$, the theorem asserts three things: the $H^1$ of the Čech data of $M_A$ on the pulled-back cover admits an $A$-linear isomorphism with $A \otimes_R H^1$ of the Čech data of $M$; its $H^0$ admits an $A$-linear isomorphism with $\ker(d \otimes_R A)$, the kernel of the base change of $d$ to $A$; and, should $A$ be flat over $R$, its $H^0$ admits an $A$-linear isomorphism with $A \otimes_R H^0$. The isomorphisms are asserted only to exist (as `Nonempty` of the respective types of linear equivalences), with no canonicity claimed.
--
--   This is the two-chart Čech form of cohomology and flat base change for a locally free sheaf of rank one: the Čech complex of the pullback is the base change of the Čech complex, so $H^1$ commutes with arbitrary base change (right exactness of $A \otimes_R -$), while $H^0$ is computed as the kernel of the base-changed differential and commutes with base change when $A$ is flat. It is used in the relative Picard computations of the project, for instance in the comparison of Euler characteristics and of fibre dimensions with kernels of base-changed Čech differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H1
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H1) ∧
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] LinearMap.ker ((𝒱.sectionsOf c M).cechDiff.baseChange A)) ∧
    (Module.Flat R A →
      Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H0)) := by sorry
