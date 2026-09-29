-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
-- name    : AutomorphicForm.setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/bc8d074d-8e32-5d64-b8de-0ede87058043
-- title:
--   Weil's integration formula on GL₂(A) along unipotent fibres
-- statement:
--   Let $A$ be a commutative normed ring that is a normed $\mathbb{R}$-algebra, finite-dimensional over $\mathbb{R}$, equipped with its Borel $\sigma$-algebra, and let $\mu$ be a measure on $A$ which is an additive Haar measure and for which $\mu$-almost every element of $A$ is a unit. Identify $2\times 2$ matrices over $A$ with functions $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to A$ via `Matrix.of`, and give this space the fourfold product measure built from $\mu$. Let $w$ be a measurable function on $2\times2$ matrices with values in $[0,\infty]$ such that, for almost every $X$ with respect to that product measure restricted to the set where $\det X$ is a unit, $\int_A^- w\bigl(X\cdot\begin{pmatrix}1&x\\0&1\end{pmatrix}\bigr)\,d\mu(x) = 1$. Let $\Psi$ be a measurable $[0,\infty]$-valued function on $(\mathrm{Fin}\,2\to A)\times A$. Then the lower Lebesgue integral of $X\mapsto w(X)\,\Psi\bigl((X_{i0})_i,\det X\bigr)\,\bigl(\mathrm{ofReal}\,|\mathrm{N}_{A/\mathbb{R}}(\det X)|\bigr)^{-2}$ over the set where $\det X$ is a unit, against the fourfold product measure, equals the iterated lower Lebesgue integral over $c$ in $A^2$ (twofold product measure) of $\int^-_{\{\delta\ \text{a unit}\}} \Psi(c,\delta)\,\bigl(\mathrm{ofReal}\,|\mathrm{N}_{A/\mathbb{R}}(\delta)|\bigr)^{-2}\,d\mu(\delta)$. Here $\mathrm{N}_{A/\mathbb{R}}$ is the algebra norm and all integrals are of $[0,\infty]$-valued functions, so no integrability is required.
--
--   This is the archimedean instance of Weil's formula $\int_G = \int_{G/N}\int_N$ for $G = \mathrm{GL}_2(A)$ and the unipotent radical $N = \{\begin{pmatrix}1&x\\0&1\end{pmatrix}\}$ of the stabiliser of the first basis vector, written without normalising constants: it computes the pushforward of $w\,|\mathrm{N}(\det X)|^{-2}\,dX$ along $X \mapsto (Xe_1, \det X)$. It feeds the computation of integrals of automorphic forms against measures on matrices over the infinite adele ring, in [`AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing`](thm.html#AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem AutomorphicForm.setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
    (A : Type) [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) (hμ : μ.IsAddHaarMeasure) (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det},
      ∫⁻ x, w (Matrix.of.symm (Matrix.of X * !![(1 : A), x; 0, 1])) ∂μ = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) *
          (ENNReal.ofReal |Algebra.norm ℝ (Matrix.of X).det| ^ 2)⁻¹
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * (ENNReal.ofReal |Algebra.norm ℝ δ| ^ 2)⁻¹ ∂μ
      ∂(Measure.pi fun _ : Fin 2 => μ) := by sorry
