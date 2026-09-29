-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/cb79707a-baee-580f-b8cb-6b44afe8a426
-- title:
--   Semilinear Γ-action on the two-chart integral model
-- statement:
--   Let $R$ be a commutative ring, $F$ a field that is an $R$-algebra, and $j \in F$ with $j \neq 0$; write $A_{\mathrm{fin}}$ for `chartAlgFin R F j`, the $R$-subalgebra of elements of $F$ integral over $R[j] =$ `Algebra.adjoin R {j}`, and $A_{\infty}$ for `chartAlgInf R F j`, the elements integral over $R[j^{-1}]$; let $\mathfrak X =$ `TwoChartIntegralModel R F j` be the pushout of `fFin` and `fInf`, with the two chart morphisms `ιFin`, `ιInf` and the structure morphism `toBase` to $\operatorname{Spec} R$ obtained by descending $\operatorname{Spec}$ of $R \to A_{\mathrm{fin}}$ and $R \to A_{\infty}$. Let $\Gamma$ be a group acting on $R$ and on $F$ by ring automorphisms, such that $s \cdot \mathrm{alg}_{R\to F}(r) = \mathrm{alg}_{R\to F}(s \cdot r)$ for all $s \in \Gamma$, $r \in R$, and $s \cdot j = j$ for all $s$. Then there are morphisms $w_s \colon \mathfrak X \to \mathfrak X$ and ring isomorphisms $\theta_s$ of $A_{\mathrm{fin}}$ and $\theta'_s$ of $A_{\infty}$, indexed by $s \in \Gamma$, such that: $w_s$ followed by `toBase` equals `toBase` followed by $\operatorname{Spec}$ of the automorphism of $R$ given by $s$; $w_1$ is the identity and $w_{ss'} = w_s$ followed by $w_{s'}$; $\theta_s$ and $\theta'_s$ act on underlying elements of $F$ by $b \mapsto s \cdot b$; `ιFin` followed by $w_s$ equals $\operatorname{Spec}(\theta_s)$ followed by `ιFin`, and likewise for `ιInf` and $\theta'_s$; and the preimage under $w_s$ of the open range of `ιFin` is that open range.
--
--   This is the Galois (or semilinear) twisting statement for the two-chart integral model: a group acting on $F$ semilinearly over its action on $R$ and fixing $j$ preserves both charts, hence acts on the glued model covering the action on the base, contravariantly in the composition so that $s \mapsto w_s$ is a genuine action after the two contravariances cancel. It is used in the construction of the Galois action on the integral model of $X_1(p)$ and in the compatibility of that action with the Abel–Jacobi map and Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

universe u v in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (Γ : Type v) [Group Γ] [MulSemiringAction Γ R] [MulSemiringAction Γ F]

    (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (hΓj : ∀ s : Γ, s • j = j) :
    ∃ (w : Γ → (AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j))
      (θ : Γ → (↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R F j)))
      (θ' : Γ → (↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R F j))),

      (∀ s : Γ, w s ≫ toBase R F j = toBase R F j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ R s))) ∧

      w 1 = 𝟙 (AlgebraicCurve.TwoChartIntegralModel R F j) ∧
      (∀ s s' : Γ, w (s * s') = w s ≫ w s') ∧

      (∀ (s : Γ) (b : ↥(chartAlgFin R F j)), ((θ s b : ↥(chartAlgFin R F j)) : F) = s • (b : F)) ∧
      (∀ (s : Γ) (b : ↥(chartAlgInf R F j)), ((θ' s b : ↥(chartAlgInf R F j)) : F) = s • (b : F)) ∧

      (∀ s : Γ, ιFin R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ιFin R F j) ∧
      (∀ s : Γ, ιInf R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ιInf R F j) ∧
      (∀ s : Γ, (w s) ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F j).opensRange) := by sorry
