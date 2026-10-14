-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_ae_lt_top
-- name    : DbarRegularity.maximalFunction_ae_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:04:52.274246+00:00
-- url     : https://prove2.me/theorems/7b1cb41a-738f-4075-9b31-3cf6556d1766
-- title:
--   The Hardy–Littlewood maximal function of an L^p function is finite almost everywhere
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure. If $f\in L^p(\mathbb{R}^d)$ for some $1\le p\le\infty$, then
--   $$Mf(x)<\infty\quad\text{for almost every }x\in\mathbb{R}^d .$$
--
--   This is part (a) of the Hardy–Littlewood maximal theorem: the supremum of the averages of an $L^p$ function over balls centred at $x$ is finite for almost every $x$.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) is `ℝ≥0∞`-valued and the conclusion is `∀ᵐ x, maximalFunction f x < ⊤` for Lebesgue measure. $p$ is in `ℝ≥0∞` with $1\le p$, so $p=\infty$ is included. This statement is conjunct (a) of `DbarRegularity.maximalFunction_bounds`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (a), p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- Stein, *Singular Integrals*, Chapter I, § 1.3, Theorem 1 (a) (p. 5): if `f ∈ L^p` for some
`1 ≤ p ≤ ∞`, then the Hardy–Littlewood maximal function `M f` is finite almost everywhere. -/
theorem maximalFunction_ae_lt_top (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤ := by sorry

end DbarRegularity
