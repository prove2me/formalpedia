-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_strongType
-- name    : DbarRegularity.maximalFunction_strongType
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:57:42.101985+00:00
-- url     : https://prove2.me/theorems/869f0c09-55e7-4b66-99be-79ee14708a7f
-- title:
--   Strong type (p,p) of the Hardy–Littlewood maximal function for 1 < p ≤ ∞
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure, and let $\|\cdot\|_p$ be the $L^p(\mathbb{R}^d)$ norm. For every $1<p\le\infty$ there is a constant $A_p$, depending only on $p$ and $d$, such that every $f\in L^p(\mathbb{R}^d)$ has $Mf\in L^p(\mathbb{R}^d)$ and
--   $$\|Mf\|_p\le A_p\,\|f\|_p.$$
--
--   This is the strong type $(p,p)$ part of the Hardy–Littlewood maximal theorem: the maximal operator is bounded on $L^p(\mathbb{R}^d)$ for every $1<p\le\infty$.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) is `ℝ≥0∞`-valued; `MemLp (maximalFunction f) p` asserts a.e. strong measurability and finite `eLpNorm`. $p$ is in `ℝ≥0∞`, so $p=\infty$ is included. The constant $A_p$ is in `ℝ≥0` and is chosen before $f$. This statement is conjunct (c) of `DbarRegularity.maximalFunction_bounds`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (c), p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

/-- Stein, *Singular Integrals*, Chapter I, § 1.3, Theorem 1 (c) (p. 5): for `1 < p ≤ ∞` there is
`A_p`, depending only on `p` and `d`, with `M f ∈ L^p` and `‖M f‖_p ≤ A_p ‖f‖_p` for `f ∈ L^p`. -/
theorem maximalFunction_strongType (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume := by sorry

end DbarRegularity
