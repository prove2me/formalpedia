-- Prove2me | Theorems.Thm_Auto_ftcCsR
-- name    : Auto.ftcCsR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:58:56.555223+00:00
-- url     : https://prove2.me/theorems/a9d5a45c-4519-4094-b01d-27ada768037e
-- title:
--   Auto: ftc Cs R
-- statement:
--   **Lemma.**
--
--   Let $0<\alpha < \beta$ and $a:[\alpha,\beta]\to \mathbb{R}$ be continuously differentiable.
--
--   Then
--
--   $$
--   \|a\|_{V_{2,J}([\alpha, \beta]; \mathbb{R})} \le (\tfrac{\beta-\alpha}{\alpha})^{1/2}
--   \|ta'(t)\|_{L^2(t\in [\alpha, \beta],\tfrac{dt}{t})},
--   $$
--
--   $$
--   \|a\|_{V_{2,J}([\alpha, \beta]; \mathbb{R})}^2 \le 8 \|a\|_{L^2([\alpha,
--   \beta],\tfrac{dt}{t})}\|ta'(t)\|_{L^2(t\in [\alpha, \beta],\tfrac{dt}{t})}.
--   $$
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1149-L1162
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1149-L1162

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.ftcCsR (J : ℕ) {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) ∧
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by sorry
