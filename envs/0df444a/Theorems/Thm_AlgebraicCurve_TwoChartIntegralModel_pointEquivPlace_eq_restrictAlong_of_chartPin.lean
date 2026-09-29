-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
-- name    : AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/61f7c702-eaff-5205-b5a3-43224e718f5e
-- title:
--   Image point's place is the restriction along Φ
-- statement:
--   Fix a commutative ring $R$, an algebraically closed field $K$ that is an $R$-algebra, and fields $F$, $F'$ over $R$ with distinguished elements $j \in F$, $j' \in F'$ assumed non-zero. Write $\mathcal{O} =$ `chartAlgFin R F j` for the subalgebra of $F$ of elements integral over $R[j]$, and $\mathcal{O}'$ for the corresponding subalgebra of $F'$; let $X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the two-chart integral model, the pushout of its two charts, with structure morphism `toBase R F j` to $\operatorname{Spec} R$ and finite chart $\iota_{\mathrm{fin}} =$ `ιFin R F j` from $\operatorname{Spec}\mathcal{O}$, and similarly for $F'$, $j'$. Let $L$, $L'$ be fields over $K$ and $\iota \colon \mathcal{O} \to L$, $\iota' \colon \mathcal{O}' \to L'$ arbitrary functions. Let $C_1$ be a `CurveModel K L`, i.e. an integral scheme $C_1.C$ with a proper smooth morphism of relative dimension $1$ to $\operatorname{Spec} K$, a ring isomorphism $C_1.\mathrm{ffEquiv} \colon L \cong$ the function field of $C_1.C$ over $K$, and a bijection from the closed points of $C_1.C$ onto the places $\mathrm{Place}\,K\,L$ (valuation subrings of $L$ containing $K$, proper, with principal ideals) realising each point's stalk as the place's valuation ring; let $e_1$ be an isomorphism from $C_1.C$ to the fibre product of `toBase R F j` with $\operatorname{Spec}(R \to K)$ whose second projection composite is $C_1.\mathrm{toBase}$, such that the preimage under $e_1$ followed by the first projection of the open image $\iota_{\mathrm{fin}} ''^{U} \top$ is non-empty, and such that this composite pulls back each $a \in \mathcal{O}$, read as a global section of the chart, to a germ at the generic point whose image under $C_1.\mathrm{ffEquiv}^{-1}$ is $\iota(a)$; let $C_2$, $e_2$ satisfy the same conditions for $F'$, $j'$, $L'$, $\iota'$. Assume given a morphism $\pi_X \colon X' \to X$ over $\operatorname{Spec} R$ and an $R$-algebra map $\theta \colon \mathcal{O} \to \mathcal{O}'$ with $\iota_{\mathrm{fin}}'$ followed by $\pi_X$ equal to $\operatorname{Spec}\theta$ followed by $\iota_{\mathrm{fin}}$, and a $K$-algebra map $\Phi \colon L \to L'$ with $\Phi(\iota(a)) = \iota'(\theta(a))$ for all $a \in \mathcal{O}$, integral as a ring map, and finite along, i.e. $L'$ is a finite module over $L$ via $\Phi$. Finally let $y$ be a section of $C_2.\mathrm{toBase}$ and $x$ a section of $C_1.\mathrm{toBase}$ over $\operatorname{Spec} K$ such that $x$ followed by $e_1$ and the first projection coincides with $y$ followed by $e_2$, the first projection and $\pi_X$. Then the place of $L$ attached to $x$ by `C₁.pointEquivPlace` equals the restriction along $\Phi$ of the place of $L'$ attached to $y$, that is, the valuation subring of the former is the preimage under $\Phi$ of the valuation subring of the latter.
--
--   This is the transport of places under a morphism of two-chart integral models that is described on the finite charts by an algebra map $\theta$, read on chart-pinned models $C_1$, $C_2$ of the fibres over an algebraically closed field $K$: points matching over the integral model have places matching under restriction along the induced field embedding. It is the geometric input for the place-theoretic description of degeneracy maps, Atkin–Lehner involutions and Hecke operators on models of modular curves, and is used by the corresponding statements for $X_H$ over a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
    (R : Type u) [CommRing R] (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]

    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F' : Type u) [Field F'] [Algebra R F'] (j' : F') [Fact (j' ≠ 0)]

    {L : Type v} [Field L] [Algebra K L] {L' : Type v} [Field L'] [Algebra K L']
    (ι : ↥(chartAlgFin R F j) → L) (ι' : ↥(chartAlgFin R F' j') → L')

    (C₁ : CurveModel K L)
    (e₁ : C₁.C ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₁]
    (he₁ : e₁ ≫ pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme
      ((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(chartAlgFin R F j),
      C₁.ffEquiv.symm
        (C₁.C.germToFunctionField
          ((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))
          (((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ιFin R F j) ''ᵁ ⊤)).hom
            (((ιFin R F j).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)))) = ι a)

    (C₂ : CurveModel K L')
    (e₂ : C₂.C ⟶ pullback (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₂]
    (he₂ : e₂ ≫ pullback.snd (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme
      ((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F' j') ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(chartAlgFin R F' j'),
      C₂.ffEquiv.symm
        (C₂.C.germToFunctionField
          ((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F' j') ''ᵁ ⊤))
          (((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ιFin R F' j') ''ᵁ ⊤)).hom
            (((ιFin R F' j').appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F' j'))).inv b)))) = ι' b)

    (πX : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hπX : πX ≫ toBase R F j = toBase R F' j')
    (θ : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'))
    (hchart : ιFin R F' j' ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ ιFin R F j)

    (Φ : L →ₐ[K] L') (hΦθ : ∀ a : ↥(chartAlgFin R F j), Φ (ι a) = ι' (θ a))
    (hint : Φ.toRingHom.IsIntegral) (hfin : FiniteAlong K Φ)

    (y : {q : Spec (CommRingCat.of K) ⟶ C₂.C // q ≫ C₂.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of K) ⟶ C₁.C // q ≫ C₁.toBase = 𝟙 _})
    (hyx : x.1 ≫ e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      y.1 ≫ e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ πX) :
    C₁.pointEquivPlace x = (C₂.pointEquivPlace y).restrictAlong Φ hint := by sorry
