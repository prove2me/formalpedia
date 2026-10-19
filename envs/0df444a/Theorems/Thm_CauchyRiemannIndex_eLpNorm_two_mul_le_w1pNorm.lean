-- Prove2me | Theorems.Thm_CauchyRiemannIndex_eLpNorm_two_mul_le_w1pNorm
-- name    : CauchyRiemannIndex.eLpNorm_two_mul_le_w1pNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T11:00:19.666587+00:00
-- url     : https://prove2.me/theorems/c46f6e36-315e-4f76-98ad-b49568742bb1
-- title:
--   Sobolev inequality $\|u\|_{L^{2p}}\le C\,\|u\|_{W^{1,p}}$ on the cylinder $\mathbb R\times S^1$
-- statement:
--   Let $1<p<\infty$ and $n\in\mathbb N$. There is a constant $C\ge0$ such that every test section $u:\mathbb R\times S^1\to\mathbb R^{2n}$ (smooth, $1$-periodic in $t$, and zero for large $|s|$) satisfies
--   $$\|u\|_{L^{2p}(\mathbb R\times S^1)}\;\le\;C\,\Big(\|u\|_{L^p}+\|\partial_s u\|_{L^p}+\|\partial_t u\|_{L^p}\Big).$$
--
--   This is the Sobolev embedding $W^{1,p}(\mathbb R\times S^1)\hookrightarrow L^{2p}(\mathbb R\times S^1)$ on the two-dimensional cylinder, with a constant that depends only on $p$ and $n$. It raises the integrability exponent of $W^{1,p}$ functions on the cylinder, for instance of elements of the kernel of a Cauchy–Riemann type operator.
--
--   **Formalization Note.** $p$ is in `ℝ≥0∞` with $1<p$, $p\ne\infty$, and $C$ is in `ℝ≥0`. The cylinder carries `cylMeasure`, Lebesgue measure on the strip $\mathbb R\times[0,1)$; test sections are `IsTestSection`, and the right-hand side is `w1pNorm p u`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.3 and Corollary 4.7, pp. 69-71; standard Sobolev space theory, e.g. H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Theorem 9.9 and Corollary 9.11

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

/-- Sobolev inequality on the cylinder `ℝ × S¹`: for `1 < p < ∞` there is a constant `C` with
`‖u‖_{L^{2p}} ≤ C ‖u‖_{W^{1,p}}` for every test section `u`. -/
theorem eLpNorm_two_mul_le_w1pNorm (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u (2 * p) cylMeasure ≤ C * w1pNorm p u := by
  sorry

end CauchyRiemannIndex
