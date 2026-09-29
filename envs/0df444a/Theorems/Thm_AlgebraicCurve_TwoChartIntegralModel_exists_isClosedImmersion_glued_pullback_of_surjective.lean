-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_glued_pullback_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/671c73c0-d9d6-5408-b9b0-66955769d182
-- title:
--   Closed immersion of a glued two-chart curve into a base change
-- statement:
--   Let $R$ be a commutative ring, $F$ a field that is an $R$-algebra, and $j \in F$ with $j \neq 0$; write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the subalgebra of elements of $F$ integral over $R[j]$ and $A_{\infty} =$ `chartAlgInf R F j` for those integral over $R[j^{-1}]$, so that [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions into the middle chart, with structure morphism `toBase R F j` to $\operatorname{Spec} R$ descended from the two algebra maps from $R$. Let $\kappa$ be a field that is an $R$-algebra, $L$ a field extension of $\kappa$, $t \in L$ with $t \neq 0$, and $m$ a positive natural number; write $\mathcal{O}\{t\} =$ `CurveModel.chartRing κ {t}` for the elements of $L$ integral over $\kappa[t]$ and $\mathcal{O}\{t^{-1}\}$ likewise, so that `CurveModel.glued κ t` is the corresponding pushout of the two charts with structure morphism `CurveModel.gluedToBase κ t` to $\operatorname{Spec}\kappa$. Assume given surjective $\kappa$-algebra homomorphisms $\theta_{\mathrm{fin}} : \kappa \otimes_R A_{\mathrm{fin}} \to \mathcal{O}\{t\}$ and $\theta_{\infty} : \kappa \otimes_R A_{\infty} \to \mathcal{O}\{t^{-1}\}$ with $\theta_{\mathrm{fin}}(1 \otimes j) = t^{m}$ and $\theta_{\infty}(1 \otimes j^{-1}) = (t^{-1})^{m}$ in $L$, and compatible in the sense that for all $b \in A_{\mathrm{fin}}$, $b' \in A_{\infty}$ and $n \in \mathbb{N}$ with $b = b' j^{n}$ in $F$ one has $\theta_{\mathrm{fin}}(1 \otimes b) = \theta_{\infty}(1 \otimes b')\, t^{mn}$ in $L$. Then there is a morphism $c$ from `CurveModel.glued κ t` to the fibre product of `toBase R F j` with $\operatorname{Spec}$ of $R \to \kappa$ such that: $c$ is a closed immersion; $c$ followed by the second projection is `CurveModel.gluedToBase κ t`; the chart morphism `CurveModel.ι₀ κ t` followed by $c$ and the first projection equals $\operatorname{Spec}$ of the ring map $b \mapsto \theta_{\mathrm{fin}}(1 \otimes b)$ followed by the chart morphism `ιFin R F j`, and correspondingly `CurveModel.ιInf κ t` with $\theta_{\infty}$ and `ιInf R F j`; a point $y$ of `CurveModel.glued κ t` is mapped by $c$ followed by the first projection into the image of the base map of `ιFin R F j` exactly when $y$ lies in the image of the base map of `CurveModel.ι₀ κ t`; and, for each point $z$ of the fibre product of `ιFin R F j` with the first projection, the image of $z$ under the second projection lies in the image of the base map of $c$ exactly when the kernel of the ring map $A_{\mathrm{fin}} \otimes_R \kappa \to \mathcal{O}\{t\}$ obtained from $\theta_{\mathrm{fin}}$ by swapping the tensor factors is contained in the prime ideal corresponding to $z$ under the canonical identification of that fibre product with $\operatorname{Spec}(A_{\mathrm{fin}} \otimes_R \kappa)$, and the same statement with $A_{\infty}$, $\theta_{\infty}$ and `ιInf R F j` in place of $A_{\mathrm{fin}}$, $\theta_{\mathrm{fin}}$ and `ιFin R F j`.
--
--   This is the general chart-by-chart criterion embedding a two-chart glued curve over $\kappa$ as a closed subscheme of the $\kappa$-fibre of the two-chart integral model attached to $(R, F, j)$, with the scaling exponent $m$ recording $j \mapsto t^{m}$; the last four clauses pin down the image of the embedding both on the glued source and on each of the two affine charts of the target. It is used in the analysis of the special fibre of the model of $X_1(p)$-type curves, where the two components arise from the exponents $m = 1$ and $m = p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_glued_pullback_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_glued_pullback_of_surjective
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hFin : Function.Surjective θFin) (hInf : Function.Surjective θInf)
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((θFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((θInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    ∃ c : CurveModel.glued κ t ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      IsClosedImmersion c ∧
      c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t ∧
      (CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j) ∧
      (CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j) ∧

      (∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base) ∧

      (∀ z : ↥(pullback (ιFin R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιFin R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θFin.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιFin R F j) ≪≫
                pullback.congrHom (ιFin_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom.base z).asIdeal) ∧
      (∀ z : ↥(pullback (ιInf R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιInf R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θInf.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιInf R F j) ≪≫
                pullback.congrHom (ιInf_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom.base z).asIdeal) := by sorry
