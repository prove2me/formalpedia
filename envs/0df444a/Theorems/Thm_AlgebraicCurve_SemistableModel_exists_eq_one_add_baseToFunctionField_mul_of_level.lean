-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level
-- name    : AlgebraicCurve.SemistableModel.exists_eq_one_add_baseToFunctionField_mul_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/8b614546-1f95-58ed-8ff3-65984c4a7e82
-- title:
--   Descent of the congruence u≡ 1 to a flat level
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$; fix the indexing data of a semistable model, namely index types $\iota_V,\iota_E$, field extensions $\overline F_i$ of the residue field of $A$, component charts $C_i$ over $A$ and $F$ with values in $\overline F_i$, annuli $An_e$, maps $\mathrm{src},\mathrm{tgt} : \iota_E \to \iota_V$ and places $xs_e$, $xt_e$ of $\overline F_{\mathrm{src}(e)}$, $\overline F_{\mathrm{tgt}(e)}$ over the residue field of $A$, and let $M$ be a semistable model for these data, with underlying integral scheme $M.X$, structure morphism $M.\mathrm{toBase} : M.X \to \operatorname{Spec} A$ and identification $M.\mathrm{ffEquiv} : F \cong K(M.X)$. Let $A_1$ be a local ring, $\iota_1 : A_1 \to A$ a local ring homomorphism such that $A_1 \to A \to A/\mathfrak m_A$ is surjective, with $\mathfrak m_{A_1} = (\varpi_1)$ for some $\varpi_1 \neq 0$, and with $\operatorname{Spec}\iota_1$ flat. Let $X_1$ be an integral scheme with a morphism $f_1 : X_1 \to \operatorname{Spec} A_1$ and let $e_1 : M.X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ be an isomorphism whose composition with the second projection is $M.\mathrm{toBase}$; write $\pi$ for $e_1$ followed by the first projection. Let $F_1 \subseteq F$ be a subfield and $\varphi_1 : F_1 \cong K(X_1)$ a ring isomorphism compatible with $\pi$ at generic points: $\pi$ maps the generic point of $M.X$ to that of $X_1$, and for every $s \in F_1$ the element $M.\mathrm{ffEquiv}(s)$ is the image of $\varphi_1(s)$ under the specialisation map into the stalk of $X_1$ at $\pi(\text{generic point})$ followed by the stalk map of $\pi$ at the generic point of $M.X$. Then, for any point $x$ of $M.X$ and any $u \in F$ lying in $F_1$: if $u = 1 + \iota(t)\,r$ for some $t \in \mathfrak m_A$ (with $\iota$ the map $A \to L \to F$) and some $r$ in the subring $\mathrm{localRing}\,M.X\,M.\mathrm{ffEquiv}\,x$ of $F$, i.e. $r$ is the preimage under $M.\mathrm{ffEquiv}$ of an element of the image of $\mathcal O_{M.X,x}$ in $K(M.X)$, then there are $t_1 \in \mathfrak m_{A_1}$ and an element $s$ in the image of $\mathcal O_{X_1,\pi(x)}$ in $K(X_1)$ with $\varphi_1(u) = 1 + \mathrm{baseToFunctionField}\,f_1(t_1)\cdot s$, where $\mathrm{baseToFunctionField}\,f_1$ is the composite $A_1 \to \Gamma(X_1,\mathcal O) \to K(X_1)$ induced by $f_1$ and the germ at the generic point. Note that the conclusion asserts only that the multiplier $t_1$ lies in $\mathfrak m_{A_1}$, rather than that $t_1 = \varpi_1$.
--
--   This is the descent step transporting a congruence $u \equiv 1$ modulo the maximal ideal of $A$, witnessed in the local ring at a point of a semistable model over $A$, to a congruence modulo the maximal ideal of $A_1$ in the local ring at the corresponding point of a flat level $X_1$ over $A_1$. It is used in the construction of Cartier data at finite level, being cited by [`AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent) and [`AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent), and it relies on [`AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback`](thm.html#AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback) and [`AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level`](thm.html#AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level.lean

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

theorem AlgebraicCurve.SemistableModel.exists_eq_one_add_baseToFunctionField_mul_of_level
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (ϖ₁ : A₁) (hϖ₁0 : ϖ₁ ≠ 0) (hϖ₁ : IsLocalRing.maximalIdeal A₁ = Ideal.span {ϖ₁})
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
    (∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
        u = 1 + algebraMap L F ((t : A) : L) * r) →
      ∃ t₁ ∈ IsLocalRing.maximalIdeal A₁,
        ∃ s ∈ (algebraMap (X₁.presheaf.stalk
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) X₁.functionField).range,
        φ₁ ⟨u, hu⟩ = 1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t₁ * s := by sorry
