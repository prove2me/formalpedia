-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
-- name    : AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/89ea548c-2773-570b-ba60-fb6e271e1f12
-- title:
--   Unfolding a cuspidal integral along rational unipotents with a weight
-- statement:
--   Let $K$ be a number field, $\mathbb{A}_K$ its adele ring, and write $n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$ for `unipotentGL2 t`. Fix functions $\varphi, f : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and a point $x\in\mathrm{GL}_2(\mathbb{A}_K)$; the measures are the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ and the additive Haar measure $\mu_{\mathbb{A}}=$ `adelicAddHaar` on $\mathbb{A}_K$, both for the Borel $\sigma$-algebras. Assume: $\varphi(n(\beta)y)=\varphi(y)$ for all $\beta\in K$ (via $K\to\mathbb{A}_K$) and all $y$; $\varphi$ is locally integrable for the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$; $\varphi$ satisfies `IsCuspidalFn` along `unipotentGL2` for the conditioning of $\mu_{\mathbb{A}}$ on the box `adelicBox K` (the adeles integral at every finite place whose infinite component lies in the fundamental domain of the lattice basis), i.e. `constantTerm` of $\varphi$ for that measure and `unipotentGL2` vanishes at every point; $f$ is continuous with compact support; $w:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{R}$ is measurable, non-negative, and $\sum_{\beta\in K}w(n(\beta)\,n(t)xc)=1$ for every $t\in\mathbb{A}_K$ and every $c$ in the topological support of $f$. Then $$\int \varphi(y)f(x^{-1}y)\,d\mu(y)=\int \varphi(y)\,w(y)\Bigl(\sum_{\beta\in K}f(x^{-1}n(\beta)y)-\mu_{\mathbb{A}}(\mathrm{box})^{-1}\int f(x^{-1}n(t)y)\,d\mu_{\mathbb{A}}(t)\Bigr)d\mu(y),$$ the sums over $K$ being `tsum`s and the normalising factor the inverse of the real number $\mu_{\mathbb{A}}(\mathtt{adelicBox}\,K)$.
--
--   This is the standard unfolding step for an integral of a cuspidal function against a left translate of a test function: the sum over the rational unipotents $n(\beta)$, $\beta\in K$, is inserted by means of a partition-of-unity weight $w$, and the constant term along the unipotent subgroup is subtracted at no cost because $\varphi$ is cuspidal. It is used in the proof of [`AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn`](thm.html#AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn), and the finiteness of the sums over $K$ rests on [`NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`](thm.html#NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
        (unipotentGL2 t * x * c)) = 1) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
            - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
