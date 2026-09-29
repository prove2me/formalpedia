-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a8a995d4-7550-59a9-8c53-a8b3e9fbbe96
-- title:
--   Finite étale block as a relative effective divisor of degree d
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a separated morphism, and let $U \subseteq C$ be an open subscheme whose inclusion followed by $c$ is smooth of relative dimension $1$. Let $A$ be an $R$-algebra that is finite and faithfully flat as an $R$-module, let $B$ be an $R$-algebra that is finite as an $R$-module and étale over $R$, let $d$ be a natural number, and suppose given an isomorphism $\varphi \colon A \otimes_R B \cong A^{d}$ of $A$-algebras. Let $z \colon \operatorname{Spec} B \to C$ be a closed immersion with $z$ followed by $c$ equal to $\operatorname{Spec}$ of the structure map $R \to B$, and assume the set-theoretic image of $z$ is contained in $U$. Then there exists a term $Z$ of type `RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of R)))`, that is, an ideal sheaf datum $Z.I$ on the fibre product of $c$ with the identity of $\operatorname{Spec} R$ such that the closed immersion of the associated subscheme followed by the second projection to $\operatorname{Spec} R$ is finite, flat and locally of finite presentation, and has fibre rank exactly $d$ at every point of $\operatorname{Spec} R$, with the two further properties that $Z.I$ is the kernel ideal sheaf of the lift of $z$ and of $\operatorname{Spec}$ of $R \to B$ to that fibre product, and that $Z$ is supported in $U$, meaning the support of $Z.I$ lies in the preimage of $U$ under the first projection.
--
--   This is the packaging step which recognises a closed subscheme of $C$ that is finite locally free of rank $d$ over the base — here the finite étale block $\operatorname{Spec} B \hookrightarrow C$, whose degree is read off after the faithfully flat base change to $A$ that splits it — as a relative effective Cartier divisor of degree $d$ for $c$, supported in the open locus $U$ where $c$ is smooth of relative dimension one. It is used in the construction of a polarisation pair from a block.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (d : ℕ) (φ : TensorProduct R A B ≃ₐ[A] (Fin d → A))
    (z : Spec (CommRingCat.of B) ⟶ C) [IsClosedImmersion z]
    (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hzU : Set.range z.base ⊆ (U : Set C)) :
    ∃ Z : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of R))),
      Z.I = (pullback.lift z (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (by rw [Category.comp_id]; exact hz)).ker ∧ Z.SupportedIn U := by sorry
