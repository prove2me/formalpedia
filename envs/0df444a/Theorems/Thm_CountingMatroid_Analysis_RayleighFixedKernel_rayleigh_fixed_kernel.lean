-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RayleighFixedKernel_rayleigh_fixed_kernel
-- name    : CountingMatroid.Analysis.RayleighFixedKernel.rayleigh_fixed_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:46:57.319852+00:00
-- url     : https://prove2.me/theorems/242a5da5-f3c9-462b-bbcc-ee40d78e798c
-- title:
--   Rayleigh inequalities force nonpositivity on a fixed functional's kernel
-- statement:
--   Let $E$ be a finite-dimensional real inner-product space, let $T:E\to E$ be a symmetric linear map, and let $\ell:E\to\mathbb R$ be linear. Suppose for every $v\in E$ that $$\ell(Tv)=\ell(v),\qquad\langle v,Tv\rangle\le\langle v,v\rangle,\qquad\langle v,Tv\rangle\le\langle Tv,Tv\rangle.$$ Assume also that $$Tv=v,\quad\ell(v)=0\quad\Longrightarrow\quad v=0.$$ Then $$\ell(v)=0\quad\Longrightarrow\quad\langle v,Tv\rangle\le0.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RayleighFixedKernel.lean#L9-L70

import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RayleighFixedKernel

open scoped BigOperators

theorem CountingMatroid.Analysis.RayleighFixedKernel.rayleigh_fixed_kernel {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (l : E →ₗ[ℝ] ℝ)
    (hinv : ∀ v, l (T v) = l v)
    (hupper : ∀ v, inner ℝ v (T v) ≤ inner ℝ v v)
    (hbound : ∀ v, inner ℝ v (T v) ≤ inner ℝ (T v) (T v))
    (hfixed : ∀ v, T v = v → l v = 0 → v = 0) :
    ∀ v, l v = 0 → inner ℝ v (T v) ≤ 0 := by sorry
