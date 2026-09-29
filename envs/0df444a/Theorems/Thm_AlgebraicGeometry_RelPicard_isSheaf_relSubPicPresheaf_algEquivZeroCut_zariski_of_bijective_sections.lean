-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/7cad5363-c564-5da9-ac35-95aaa09b5967
-- title:
--   Zariski sheaf property of the fibrewise Pic⁰ presheaf
-- statement:
--   Fix a universe $u$, a commutative ring $R$, a scheme $C$ and a morphism $c : C \to \operatorname{Spec} R$, together with $\varepsilon$, an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume the hypothesis `hH0`: for every $R$-algebra $A$, the canonical map from $A$ to the global sections $\Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ — the algebra structure induced by the second projection of the pullback of $c$ along $\operatorname{Spec}$ of the structure map $R \to A$ — is bijective. The conclusion is that the presheaf `relSubPicPresheaf c ε (algEquivZeroCut c ε)` on $(\mathrm{Over}\,(\operatorname{Spec} R))^{\mathrm{op}}$, valued in `Type (u+1)`, satisfies `Presieve.IsSheaf` for the Zariski topology of schemes transported to the over-category of $\operatorname{Spec} R$. Here the presheaf is the subfunctor of `relPicardPresheaf c ε` whose sections over an object $t : T \to \operatorname{Spec} R$ are those isomorphism classes of rigidified line bundles satisfying the condition `algEquivZeroCut`, namely `FibrewiseAlgEquivZero`: a representative $M$ has the property that for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$, the pullback of $M.L$ to the corresponding geometric fibre of $c$ is algebraically equivalent to zero; this condition is preserved by isomorphism and by pullback and holds for the unit bundle.
--
--   This is the statement that the relative $\mathrm{Pic}^0$ functor attached to $c$ and its section $\varepsilon$, cut out by fibrewise algebraic equivalence to zero, is a Zariski sheaf on $R$-schemes, under the hypothesis that formation of global sections of $C$ commutes with base change and gives back the base ring. It is the descent input used in the construction of relative Picard schemes: the sheaf property is invoked when producing open charts for this functor and when assembling a representing scheme from local data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by sorry
