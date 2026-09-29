-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_le_preimage_forall_mem_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/802bf790-e84f-51f9-a9c7-80bd18f510da
-- title:
--   Affine neighbourhood of a finite set in an open, over an affine base open
-- statement:
--   Let $R$ be a commutative ring, $F$ a field that is an $R$-algebra, and $j \in F$ a nonzero element. Write $X$ for the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), namely the pushout in schemes of the two morphisms $\operatorname{Spec}$ of the inclusions of the subalgebras $\operatorname{chartAlg} R F \{j\}$ and $\operatorname{chartAlg} R F \{j^{-1}\}$ of $F$ into the middle chart, and write `toBase R F j` for the morphism $X \to \operatorname{Spec} R$ obtained from the pushout property out of the two structure morphisms $\operatorname{Spec}$ of $R \to \operatorname{chartAlg} R F \{j\}$ and $R \to \operatorname{chartAlg} R F \{j^{-1}\}$, which agree on the middle chart. Let $U$ be an open of $X$, let $V$ be an affine open of $\operatorname{Spec} R$, and let $S$ be a finite set of points of $U$ such that each $x \in S$ has image in $V$ under the composite of the inclusion $U \hookrightarrow X$ followed by `toBase R F j`. Then there is an open $W$ of the scheme $U$ such that $W$ is an affine open, $W$ is contained in the preimage of $V$ under that composite, and every $x \in S$ lies in $W$.
--
--   This is the usual statement that finitely many points of a scheme with the property that any finite subset lies in a single affine open admit an affine neighbourhood inside a prescribed open and over a prescribed affine open of the base, specialised to the two-chart integral model. It supplies the affine-covering hypothesis used in the representability argument for the relative $\mathrm{Pic}^0$ of such models, as cited by [`ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le`](thm.html#ModularCurve.XHDRModelAtP.exists_representsRelSubPic_algEquivZeroCut_epsInf_of_atkinLehner_generic_of_ker_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_le_preimage_forall_mem_of_finset
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (U : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens)
    (V : (Spec (CommRingCat.of R)).affineOpens) (S : Finset ↥U)
    (hS : ∀ x ∈ S, (U.ι ≫ toBase R F j).base x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
      W ≤ (U.ι ≫ toBase R F j) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ S, x ∈ W := by sorry
