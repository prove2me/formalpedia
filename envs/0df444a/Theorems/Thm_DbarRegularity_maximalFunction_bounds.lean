-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_bounds
-- name    : DbarRegularity.maximalFunction_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:52:28.195357+00:00
-- url     : https://prove2.me/theorems/fd9ca72f-94e4-422e-a369-9656fe42bfb8
-- title:
--   The Hardy–Littlewood maximal theorem
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$. $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Then:
--
--   1. if $f\in L^p(\mathbb{R}^d)$ for some $1\le p\le\infty$, then $Mf(x)<\infty$ for almost every $x$;
--   2. there is a constant $A$ depending only on $d$ such that for every $f\in L^1(\mathbb{R}^d)$ and every $\alpha>0$,
--   $$m\{x: Mf(x)>\alpha\}\le\frac{A}{\alpha}\int_{\mathbb{R}^d}|f|\,dx;$$
--   3. for every $1<p\le\infty$ there is a constant $A_p$ depending only on $p$ and $d$ such that every $f\in L^p(\mathbb{R}^d)$ has $Mf\in L^p(\mathbb{R}^d)$ and $\|Mf\|_p\le A_p\|f\|_p$.
--
--   **Formalization Note** `maximalFunction f` is valued in `ℝ≥0∞`; part 3 asserts `MemLp (maximalFunction f) p` and bounds its `eLpNorm`. $p$ is in `ℝ≥0∞`, so $p=\infty$ is included in parts 1 and 3. The constants are in `ℝ≥0` and are chosen before $f$ (and $\alpha$). Stein remarks that $A=5^d$ will do in part 2; the statement asks only for some constant depending on $d$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter I, § 1.3, Theorem 1, p. 5

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter I, § 1.3, Theorem 1 (p. 5): the Hardy–Littlewood maximal
function `M f` of `f` on `ℝ^d`
(a) is finite almost everywhere when `f ∈ L^p`, `1 ≤ p ≤ ∞`;
(b) is of weak type `(1, 1)`: `|{M f > α}| ≤ (A / α) ‖f‖₁` with `A` depending only on `d`;
(c) is in `L^p` with `‖M f‖_p ≤ A_p ‖f‖_p` when `f ∈ L^p`, `1 < p ≤ ∞`, with `A_p` depending only
on `p` and `d`. -/
theorem maximalFunction_bounds (d : ℕ) :
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤) ∧
    (∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Integrable f → ∀ α : ℝ≥0, 0 < α →
      volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤ (A : ℝ≥0∞) / α * ∫⁻ x, ‖f x‖ₑ) ∧
    (∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume) := by sorry

end DbarRegularity
