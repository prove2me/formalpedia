-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_comp_eq_id_of_retraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/dc1d5879-2fed-5b70-9b1d-bf2a46e45b44
-- title:
--   Retraction of finite-chart algebras yields a closed-immersion section of the fibre
-- statement:
--   Let $R$ be a commutative ring, let $F$ and $F_0$ be fields that are $R$-algebras, and let $j \in F$, $j_0 \in F_0$ be nonzero. For such data the two-chart integral model $\mathfrak X(R,F,j)$ is the pushout of the two maps $\operatorname{Spec}$ of the inclusions of the integral closure of $R[j]$ in $F$ (written `chartAlgFin R F j`: the elements of $F$ integral over $R[j]$) and of the integral closure of $R[j^{-1}]$, with structure morphism `toBase R F j` to $\operatorname{Spec} R$; assume `toBase R F j` and `toBase R F₀ j₀` are proper. Assume given a morphism $\pi \colon \mathfrak X(R,F,j) \to \mathfrak X(R,F_0,j_0)$ over $\operatorname{Spec} R$ and an $R$-algebra map $\iota \colon A^0_{\mathrm{fin}} \to A_{\mathrm{fin}}$ between the two finite-chart algebras such that the finite-chart morphism `ιFin R F j` followed by $\pi$ equals $\operatorname{Spec}(\iota)$ followed by `ιFin R F₀ j₀`. Let $\kappa$ be a field that is an $R$-algebra such that the fibre $P_0 = \mathfrak X(R,F_0,j_0) \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa$ is an integral scheme whose projection to $\operatorname{Spec} \kappa$ is smooth of relative dimension $1$, and such that $\kappa \otimes_R A^0_{\mathrm{fin}}$ is nontrivial. Let $\pi_\kappa \colon P \to P_0$ be a morphism between the two fibres compatible with $\pi$ on the first projections and with the projections to $\operatorname{Spec} \kappa$; let $c_0 \colon \operatorname{Spec}(\kappa \otimes_R A^0_{\mathrm{fin}}) \to P_0$ and $c \colon \operatorname{Spec}(\kappa \otimes_R A_{\mathrm{fin}}) \to P$ be morphisms whose first components are $\operatorname{Spec}$ of the right inclusion followed by the respective finite-chart morphism and whose second components are $\operatorname{Spec}$ of the left inclusion of $\kappa$. Finally let $\sigma_0 \colon \kappa \otimes_R A_{\mathrm{fin}} \to \kappa \otimes_R A^0_{\mathrm{fin}}$ be a $\kappa$-algebra map with $\sigma_0 \circ (\mathrm{id}_\kappa \otimes \iota) = \mathrm{id}$. Then there exists a morphism $\mathrm{comp}_0 \colon P_0 \to P$ over $\operatorname{Spec} \kappa$ which is a closed immersion, satisfies $\pi_\kappa \circ \mathrm{comp}_0 = \mathrm{id}_{P_0}$, satisfies $\mathrm{comp}_0 \circ c_0 = c \circ \operatorname{Spec}(\sigma_0)$, and has the property that a point $x$ of $P_0$ lies in the image of $c_0$ whenever its image under $\mathrm{comp}_0$ lies in the image of $c$.
--
--   This is a level-free form of the construction, on two-chart integral models of function fields, of a component of a special fibre as a section of a degeneracy map: a retraction of the finite-chart algebras after base change to $\kappa$ extends across the complement of the finite chart to a closed immersion of the whole fibre. It is used in the analysis of the Deligne–Rapoport model of a modular curve at a prime exactly dividing the level, via [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart), and the extension step rests on the valuative extension criterion for maps from a regular curve to a proper scheme ([`AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk`](thm.html#AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk)), combined with the discreteness of the local rings at closed points of a smooth integral curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_comp_eq_id_of_retraction
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₀ : Type u) [Field F₀] [Algebra R F₀] (j₀ : F₀) [Fact (j₀ ≠ 0)]
    [IsProper (toBase R F j)] [IsProper (toBase R F₀ j₀)]

    (π : TwoChartIntegralModel R F j ⟶ TwoChartIntegralModel R F₀ j₀) (hπ : π ≫ toBase R F₀ j₀ = toBase R F j)
    (ι : ↥(chartAlgFin R F₀ j₀) →ₐ[R] ↥(chartAlgFin R F j))
    (hπchart : ιFin R F j ≫ π = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ιFin R F₀ j₀)

    (κ : Type u) [Field κ] [Algebra R κ]
    [IsIntegral (pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [SmoothOfRelativeDimension 1
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [Nontrivial (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))]

    (πκ : pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hπκfst : πκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π)
    (hπκsnd : πκ ≫ pullback.snd _ _ = pullback.snd _ _)

    (c₀ : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀))).toRingHom) ≫ ιFin R F₀ j₀)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀)))))
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (σ₀ : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] κ ⊗[R] ↥(chartAlgFin R F₀ j₀))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z) :
    ∃ comp₀ : pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      comp₀ ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion comp₀ ∧
      comp₀ ≫ πκ = 𝟙 _ ∧
      c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧

      (∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by sorry
