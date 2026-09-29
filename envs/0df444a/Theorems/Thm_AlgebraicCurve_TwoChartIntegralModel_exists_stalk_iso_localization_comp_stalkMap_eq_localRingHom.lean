-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e4a14e08-18aa-5f4f-b01c-136ca6d394cf
-- title:
--   Stalk map of a comparison morphism of two-chart models
-- statement:
--   Let $R$ be a commutative ring, let $F$ be a field with an $R$-algebra structure and $j \in F$ a nonzero element, and likewise $F_1$ a field over $R$ with $j_1 \in F_1$ nonzero. Write $A =$ `chartAlgFin R F j` for the subalgebra of $F$ consisting of the elements integral over $R[j]$, and $A_1 =$ `chartAlgFin R F₁ j₁` for the analogous subalgebra of $F_1$; the two-chart integral models $X =$ `TwoChartIntegralModel R F j` and $X_1$ are the pushouts of the two chart morphisms, carrying morphisms `toBase` to $\operatorname{Spec} R$ and morphisms `ιFin` from the finite charts $\operatorname{Spec} A$, $\operatorname{Spec} A_1$. Given an $R$-algebra map $\iota_F \colon A_1 \to A$, a morphism of schemes $m \colon X \to X_1$ with $\operatorname{Spec}(\iota_F)$ followed by `ιFin R F₁ j₁` equal to `ιFin R F j` followed by $m$, and a point $y$ of $\operatorname{Spec} A$ with prime ideal $\mathfrak p = y.\mathrm{asIdeal}$, the assertion is the existence of isomorphisms of commutative rings $e \colon \mathcal{O}_{X, \iota_{\mathrm{Fin}}(y)} \cong A_{\mathfrak p}$ and $e_1 \colon \mathcal{O}_{X_1, m(\iota_{\mathrm{Fin}}(y))} \cong (A_1)_{\iota_F^{-1}(\mathfrak p)}$ such that: for every $r \in R$, $e$ sends the germ at $\iota_{\mathrm{Fin}}(y)$ of the global section of $X$ obtained from $r$ through `toBase` (via the inverse of `Scheme.ΓSpecIso`) to the image of $r$ under $R \to A_{\mathfrak p}$; the same holds for $e_1$ with `toBase R F₁ j₁` and $R \to (A_1)_{\iota_F^{-1}(\mathfrak p)}$; and $e_1$ followed by `Localization.localRingHom` of $\iota_F$ at $\iota_F^{-1}(\mathfrak p)$ and $\mathfrak p$ equals the stalk map of $m$ at $\iota_{\mathrm{Fin}}(y)$ followed by $e$.
--
--   This is the dictionary identifying, at a point of the finite chart, the stalk map of a comparison morphism of two-chart integral models with the canonical map of localised chart rings, together with the normalisation that germs coming from the base ring $R$ correspond to the images of $R$ in the localisations. It is used in the study of models of modular curves, where properties of $m$ at a point (finiteness, ramification, residue fields, the image of a uniformiser) are read off from the $R$-algebra map $\iota_F$ of chart rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₁ : Type u) [Field F₁] [Algebra R F₁] (j₁ : F₁) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin R F₁ j₁) →ₐ[R] ↥(chartAlgFin R F j))
    (m : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F₁ j₁)
    (hmF : Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F₁ j₁ = ιFin R F j ≫ m)
    (y : ↥(XFin R F j)) :
    ∃ (e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅
          CommRingCat.of (Localization.AtPrime y.asIdeal))
      (e₁ : (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk (m.base ((ιFin R F j).base y)) ≅
          CommRingCat.of (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom))),
      (∀ r : R, e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ r : R, e₁.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.germ ⊤ (m.base ((ιFin R F j).base y)) trivial).hom
            (((toBase R F₁ j₁).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom)) r) ∧
      e₁.hom ≫ CommRingCat.ofHom
          (Localization.localRingHom (y.asIdeal.comap ιF.toRingHom) y.asIdeal ιF.toRingHom rfl) =
        m.stalkMap ((ιFin R F j).base y) ≫ e.hom := by sorry
