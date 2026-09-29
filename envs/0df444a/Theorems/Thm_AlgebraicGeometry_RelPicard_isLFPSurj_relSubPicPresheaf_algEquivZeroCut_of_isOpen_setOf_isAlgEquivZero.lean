-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
-- name    : AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/a8729e53-7542-5678-b06c-377fe16253bb
-- title:
--   Limit surjectivity for the Pic⁰ cut, given openness and point-independence
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a proper flat morphism of schemes, let $\mathcal V$ be a two-affine open cover of $C$ (two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine), and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Two hypotheses are imposed on the locus where a rigidified line bundle is algebraically equivalent to zero on geometric fibres, the predicate `IsAlgEquivZero` asserting the existence of a geometrically integral base $T' \to \operatorname{Spec} k$ locally of finite type, an invertible module $M$ on the fibre base-changed to $T'$, and two sections $t_0, t_1$ of $T'$ over $\operatorname{Spec} k$ along which $M$ becomes, respectively, the unit module and the given bundle. First, (openness) for every $R$-scheme $t \colon T \to \operatorname{Spec} R$ locally of finite type and every rigidified line bundle $L$ on $C \times_R T$ (an invertible module trivialised along the section induced by $\varepsilon$), the set of $x \in T$ such that `IsAlgEquivZero` holds for the fibre of $L$ at every morphism $s \colon \operatorname{Spec} k \to T$ with $k$ algebraically closed and set-theoretic image contained in $\{x\}$ is open in $T$. Second, (independence of the geometric point) for such $t$, $L$ and any $x \in T$, if `IsAlgEquivZero` holds for the fibre at one such $s_1$ with image in $\{x\}$, then it holds for every such $s_2$. The conclusion is `IsLFPSurj` for the subpresheaf of the rigidified relative Picard presheaf of $(c, \varepsilon)$ cut out by the condition that a class be fibrewise algebraically equivalent to zero: for every $R$-algebra $A$ and every element of that presheaf at $\operatorname{Spec} A$ viewed over $\operatorname{Spec} R$, there are a finitely generated $R$-subalgebra $A_0 \subseteq A$ and an element at $\operatorname{Spec} A_0$ whose pullback along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ is the given element.
--
--   This is the surjectivity half of the statement that the identity component of the relative Picard functor of a pointed proper flat curve is locally of finite presentation: every class over an $R$-algebra $A$ descends to a finitely generated $R$-subalgebra; no uniqueness or injectivity assertion is made. Stated with openness of the $\mathrm{Pic}^0$ locus and independence of the chosen geometric point as hypotheses rather than derived from smoothness, it is applied in the constructions of the relative $\mathrm{Pic}^0$ for families of lines and of glued smooth curves, where those two inputs are supplied separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.AffineLimit
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hopen : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t),
      IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)})
    (hpt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (x : T)
      {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T),
      Set.range ⇑s₁ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₁) (fibreModule c t s₁ L.L) →
      ∀ {k₂ : Type u} [Field k₂] [IsAlgClosed k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T),
      Set.range ⇑s₂ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₂) (fibreModule c t s₂ L.L)) :
    IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by sorry
