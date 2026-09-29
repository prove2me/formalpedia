-- Prove2me | Theorems.Thm_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul
-- name    : DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/80313237-5de7-5680-9465-afc9b6290054
-- title:
--   Dixmier–Malliavin factorisation on a finite-dimensional real algebra
-- statement:
--   Let $A$ be a normed ring which is a normed algebra over $\mathbb{R}$ and finite-dimensional over $\mathbb{R}$, equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $A$. Let $U$ be a neighbourhood of the multiplicative unit $1 \in A$, and let $\Phi : A \to \mathbb{C}$ be a $C^\infty$ function (smooth in the real sense, of order $\top$) with compact support. The assertion is that there exist a natural number $n$ and families $\Phi', \Psi : \mathrm{Fin}\,n \to (A \to \mathbb{C})$ such that: each $\Phi'_k$ is $C^\infty$ with topological support contained in the topological support of $\Phi$ (hence itself compactly supported); each $\Psi_k$ is $C^\infty$, compactly supported, with topological support contained in $U$; and for every $x \in A$, $$\Phi(x) = \sum_{k} \int_A \Phi'_k(x y)\, \Psi_k(y)\, d\mu(y),$$ the product $xy$ being the ring multiplication of $A$. The identity is asserted at every $x \in A$, with no invertibility restriction, and the number $n$ of terms is not controlled.
--
--   This is the Dixmier–Malliavin factorisation theorem in the form that a smooth compactly supported function on $A$ is a finite sum of right convolutions by smooth functions supported in an arbitrarily small neighbourhood of $1$, the convolution being taken for the ring multiplication against an additive Haar measure. It is used in the treatment of test functions for automorphic forms, via [`AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn), and is obtained from the one-parameter statement [`DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add`](thm.html#DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add) along exponentials of elements of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul.lean

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
    (μ : MeasureTheory.Measure A) [μ.IsAddHaarMeasure] (U : Set A) (hU : U ∈ nhds (1 : A))
    (Φ : A → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (Φ' Ψ : Fin n → A → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U) ∧
      ∀ x : A, Φ x = ∑ k, ∫ y, Φ' k (x * y) * Ψ k y ∂μ := by sorry
