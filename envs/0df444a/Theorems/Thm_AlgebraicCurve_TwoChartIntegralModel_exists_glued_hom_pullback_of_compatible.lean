-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_glued_hom_pullback_of_compatible
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_glued_hom_pullback_of_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/ef38ff32-8840-50c4-8d10-fa8496ba56a7
-- title:
--   Glued two-chart curve mapping to the base-changed integral model
-- statement:
--   Let $R$ be a commutative ring, $F$ a field with an $R$-algebra structure and $j \in F$ nonzero; write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` and $A_{\mathrm{inf}} =$ `chartAlgInf R F j` for the $R$-subalgebras of $F$ consisting of the elements integral over $R[j]$, resp. over $R[j^{-1}]$, and let `TwoChartIntegralModel R F j` be the scheme obtained by gluing $\operatorname{Spec} A_{\mathrm{fin}}$ and $\operatorname{Spec} A_{\mathrm{inf}}$ along the middle chart, with chart morphisms `ιFin R F j`, `ιInf R F j` and structure morphism `toBase R F j` to $\operatorname{Spec} R$. Let $\kappa$ be a field with an $R$-algebra structure, $L$ a field extension of $\kappa$, $t \in L$ nonzero, and $m$ a positive natural number; write $B_{0} =$ `CurveModel.chartRing κ {t}` and $B_{\infty} =$ `CurveModel.chartRing κ {t⁻¹}` for the $\kappa$-subalgebras of $L$ of elements integral over $\kappa[t]$, resp. $\kappa[t^{-1}]$, and `CurveModel.glued κ t` for the scheme glued from $\operatorname{Spec} B_0$ and $\operatorname{Spec} B_\infty$, with chart morphisms `CurveModel.ι₀ κ t`, `CurveModel.ιInf κ t` and structure morphism `CurveModel.gluedToBase κ t` to $\operatorname{Spec}\kappa$. Suppose given $\kappa$-algebra maps $\theta_{\mathrm{fin}} \colon \kappa \otimes_R A_{\mathrm{fin}} \to B_0$ and $\theta_{\inf} \colon \kappa \otimes_R A_{\inf} \to B_\infty$ (no surjectivity assumed) such that, in $L$, $\theta_{\mathrm{fin}}(1 \otimes j) = t^{m}$ and $\theta_{\inf}(1 \otimes j^{-1}) = (t^{-1})^{m}$, and which are compatible in the sense that whenever $b \in A_{\mathrm{fin}}$, $b' \in A_{\inf}$ and $n \in \mathbb{N}$ satisfy $b = b' j^{n}$ in $F$, one has $\theta_{\mathrm{fin}}(1 \otimes b) = \theta_{\inf}(1 \otimes b')\, t^{mn}$ in $L$. Then there exists a morphism $c$ from `CurveModel.glued κ t` to the fibre product of `toBase R F j` with $\operatorname{Spec}$ of the structure map $R \to \kappa$, such that: $c$ followed by the second projection is `CurveModel.gluedToBase κ t`; the composite of `CurveModel.ι₀ κ t` with $c$ followed by the first projection equals $\operatorname{Spec}$ of the ring map $b \mapsto \theta_{\mathrm{fin}}(1 \otimes b)$ followed by `ιFin R F j`; the composite of `CurveModel.ιInf κ t` with $c$ followed by the first projection equals $\operatorname{Spec}$ of $b \mapsto \theta_{\inf}(1 \otimes b)$ followed by `ιInf R F j`; and for every point $y$ of `CurveModel.glued κ t`, the image of $y$ under the map of underlying spaces of $c$ followed by the first projection lies in the range of the underlying map of `ιFin R F j` if and only if $y$ lies in the range of the underlying map of `CurveModel.ι₀ κ t`.
--
--   This is the gluing step that produces, from a compatible pair of chart-level algebra maps, a $\kappa$-morphism from a two-chart smooth model of $L$ into the $\kappa$-fibre of the two-chart integral model, together with the chart-by-chart description of the morphism and the matching of the two chart decompositions at the level of points; it is the version of the construction in which the chart maps are not assumed surjective, so the conclusion is a morphism rather than a closed immersion. It is used in the identification of the components of the special fibre of the modular curve $X_1(p)$ with explicit two-chart models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_glued_hom_pullback_of_compatible.lean

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

theorem AlgebraicCurve.TwoChartIntegralModel.exists_glued_hom_pullback_of_compatible
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n →
      ((θFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((θInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    ∃ c : CurveModel.glued κ t ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
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
          y ∈ Set.range (CurveModel.ι₀ κ t).base) := by sorry
