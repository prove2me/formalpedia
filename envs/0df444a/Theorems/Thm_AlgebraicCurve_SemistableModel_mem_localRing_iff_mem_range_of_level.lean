-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_mem_localRing_iff_mem_range_of_level
-- name    : AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e2bbfd62-6811-590a-a957-deb7fdd6c448
-- title:
--   Regularity descends along a flat level of a semistable model
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F/L$ a field extension, and let $M$ be a `SemistableModel` for the data consisting of component charts $C_i$ (one for each $i \in \iota_V$, with values in residue extensions $\bar F_i$ of the residue field of $A$), annuli $An_e$ ($e \in \iota_E$) with source and target maps $\mathrm{src}, \mathrm{tgt} : \iota_E \to \iota_V$ and prescribed boundary places $xs_e, xt_e$; so $M$ supplies an integral scheme $M.X$ proper, flat and locally of finite presentation over $\operatorname{Spec} A$ together with an isomorphism $M.\mathrm{ffEquiv} : F \cong K(M.X)$ and the charted classification of its points. Let $A_1$ be a local ring, $\iota_1 : A_1 \to A$ a local ring homomorphism whose composition with the residue map of $A$ is surjective and such that $\operatorname{Spec}(\iota_1)$ is flat, let $X_1$ be an integral scheme with a morphism $f_1 : X_1 \to \operatorname{Spec} A_1$, and let $e_1$ be an isomorphism $M.X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ whose composition with the second projection is $M.\mathrm{toBase}$. Write $\pi$ for $e_1$ followed by the first projection, so $\pi : M.X \to X_1$. Let $F_1 \subseteq F$ be a subfield and $\varphi_1 : F_1 \cong K(X_1)$ a ring isomorphism, and assume the generic-point compatibility: there is an equality $\pi(\eta_{M.X}) = \eta_{X_1}$ such that for all $s \in F_1$ the element $M.\mathrm{ffEquiv}(s)$ is the image of $\varphi_1(s)$ under the specialisation map into the stalk of $X_1$ at $\pi(\eta_{M.X})$ followed by the stalk map of $\pi$ at $\eta_{M.X}$. Then for every point $x$ of $M.X$ and every $u \in F$ lying in $F_1$: $u$ belongs to `SemistableModel.localRing M.X M.ffEquiv x`, that is to the subring of $F$ obtained by transporting the image of $\mathcal O_{M.X,x} \to K(M.X)$ along $M.\mathrm{ffEquiv}^{-1}$, if and only if $\varphi_1(u)$ lies in the image of $\mathcal O_{X_1,\pi(x)} \to K(X_1)$.
--
--   This is the statement that, for functions coming from the level field $F_1$, regularity at a point of a semistable model is equivalent to regularity at the image point downstairs: $\mathcal O_{X_1,\pi x} = \mathcal O_{X,x} \cap K(X_1)$ inside $K(X)$ for a flat $\pi$. It is the level-transfer device used in the descent of Cartier data and of unit conditions from a semistable model to a finite level, and is cited in the construction of Kummer-type Cartier data at finite level and in the production of functions congruent to $1$ along the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_mem_localRing_iff_mem_range_of_level.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    [Flat (Spec.map (CommRingCat.ofHom ι₁))]
    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))
    (x : M.X) (u : F) (hu : u ∈ F₁) :
    (u ∈ SemistableModel.localRing M.X M.ffEquiv x ↔
      φ₁ ⟨u, hu⟩ ∈ (algebraMap (X₁.presheaf.stalk
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) X₁.functionField).range) := by sorry
