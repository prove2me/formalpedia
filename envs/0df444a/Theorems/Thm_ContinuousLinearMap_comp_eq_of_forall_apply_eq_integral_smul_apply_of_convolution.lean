-- Prove2me | Theorems.Thm_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
-- name    : ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6c9a1745-ce6e-57a6-96e1-668dfd9cf7a0
-- title:
--   Weighted averages of a compact group representation compose by convolution
-- statement:
--   Let $C$ be a compact Hausdorff topological group with its Borel $\sigma$-algebra, equipped with a Haar measure $\mu$ that is a probability measure, and let $H$ be a complex inner product space that is complete. Let $S : C \to (H \to_{L} H)$ be a multiplicative homomorphism into the bounded $\mathbb{C}$-linear operators on $H$, let $B \in \mathbb{R}$ be such that $\|S(c)\| \le B$ for all $c \in C$, and assume that $c \mapsto S(c)v$ is continuous for every $v \in H$. Two assertions are made simultaneously. First, for all continuous $w_1, w_2 : C \to \mathbb{C}$ and all bounded operators $A_1, A_2, A_{12}$ on $H$ satisfying $A_1 v = \int_C w_1(c)\,S(c)v\,d\mu(c)$, $A_2 v = \int_C w_2(c)\,S(c)v\,d\mu(c)$ and $A_{12} v = \int_C \bigl(\int_C w_1(d)\,w_2(d^{-1}c)\,d\mu(d)\bigr)S(c)v\,d\mu(c)$ for all $v \in H$, the composite of $A_2$ followed by $A_1$ equals $A_{12}$. Second, for every bounded operator $A$ on $H$ with $A v = \int_C S(c)v\,d\mu(c)$ for all $v$: $A v = v$ holds if and only if $S(c)v = v$ for all $c \in C$, and $A \circ A = A$.
--
--   This is the standard composition rule for weighted averages of a uniformly bounded strongly continuous representation of a compact group over Haar probability measure — composition corresponds to convolution of the weight functions — together with the statement that the unweighted average is the idempotent projection onto the subspace of $S$-fixed vectors. It is used to produce an idempotent level-averaging operator on a cuspidal spectrum, via [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v) :
    (∀ (w₁ w₂ : C → ℂ), Continuous w₁ → Continuous w₂ →
      ∀ (A₁ A₂ A₁₂ : H →L[ℂ] H),
        (∀ v : H, A₁ v = ∫ c, (w₁ c) • (S c v) ∂μ) → (∀ v : H, A₂ v = ∫ c, (w₂ c) • (S c v) ∂μ) →
        (∀ v : H, A₁₂ v = ∫ c, (∫ d, w₁ d * w₂ (d⁻¹ * c) ∂μ) • (S c v) ∂μ) →
        A₁.comp A₂ = A₁₂) ∧
    (∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ c, S c v ∂μ) →
      (∀ v : H, A v = v ↔ ∀ c : C, S c v = v) ∧ A.comp A = A) := by sorry
