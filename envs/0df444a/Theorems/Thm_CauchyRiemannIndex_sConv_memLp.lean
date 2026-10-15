-- Prove2me | Theorems.Thm_CauchyRiemannIndex_sConv_memLp
-- name    : CauchyRiemannIndex.sConv_memLp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T08:39:34.12766+00:00
-- url     : https://prove2.me/theorems/ce4f95fe-c16f-49bf-aea0-2d25f76fda26
-- title:
--   Convolution in the $s$-variable maps $L^q(\mathbb R\times S^1)$ into itself
-- statement:
--   Let $1\le q\le\infty$, let $g\in L^q(\mathbb R\times S^1,\mathbb R^{2n})$, where $S^1=\mathbb R/\mathbb Z$, and let $\rho:\mathbb R\to\mathbb R$ be continuous and integrable. Then the convolution of $g$ with $\rho$ in the first variable,
--   $$G(s,t)=\int_{\mathbb R}\rho(\sigma)\,g(s-\sigma,t)\,d\sigma ,$$
--   also lies in $L^q(\mathbb R\times S^1,\mathbb R^{2n})$.
--
--   Smoothing in the translation direction $s$ of the cylinder $\mathbb R\times S^1$ is the standard way to regularize functions in that direction, for example annihilators of the range of translation-invariant operators $\partial_s+J_0\partial_t+S_\infty(t)$ (Wendl, Lecture 4). This statement says that the operation stays in $L^q$ for every exponent $1\le q\le\infty$.
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)` and $L^q(\mathbb R\times S^1)$ is `LpCyl n q`, i.e. $L^q$ of Lebesgue measure on the strip $\mathbb R\times[0,1)$ (`cylMeasure`). $G$ is defined pointwise from the chosen representative of $g$ by a Bochner integral over $\sigma\in\mathbb R$, and the conclusion is `MemLp G q cylMeasure`. Integrable means `Integrable ρ` for Lebesgue measure.
-- source:
--   Standard (convolution estimates in one variable); setting of C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, §4.1

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- For `g ∈ L^q(ℝ × S¹, ℝ²ⁿ)` (`1 ≤ q ≤ ∞`) and a continuous integrable `ρ : ℝ → ℝ`, the
convolution of `g` with `ρ` in the `s`-variable, `G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`, lies in
`L^q(ℝ × S¹, ℝ²ⁿ)`. -/
theorem sConv_memLp (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hρi : Integrable ρ) :
    MemLp (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) q cylMeasure := by
  sorry

end CauchyRiemannIndex
