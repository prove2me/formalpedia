-- Prove2me | Theorems.Thm_CauchyRiemannIndex_tendsto_eLpNorm_zero_of_dominated
-- name    : CauchyRiemannIndex.tendsto_eLpNorm_zero_of_dominated
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T23:20:59.892897+00:00
-- url     : https://prove2.me/theorems/73f9bfd5-b5ab-4125-8702-4d452b2ad6c4
-- title:
--   Dominated convergence in $L^p$, $0<p<\infty$
-- statement:
--   Let $\mu$ be a measure, $E$ a normed space and $0<p<\infty$. Let $F_k:\alpha\to E$ be a.e. strongly measurable and $b\in L^p(\mu)$ a real function with $\|F_k(x)\|\le b(x)$ for a.e. $x$ and every $k$. If $F_k(x)\to0$ for a.e. $x$, then
--   $$\lim_{k\to\infty}\|F_k\|_{L^p(\mu)}=0.$$
--
--   This is the dominated convergence theorem in $L^p$ norm, the standard tool for passing to the limit in $L^p$ under a pointwise bound.
--
--   **Formalization Note.** The conclusion is `Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0)` in `ℝ≥0∞`; $p\in$ `ℝ≥0∞` with $p\ne0$, $p\ne\infty$.
-- source:
--   H. Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations, Springer 2011, Theorem 4.2 (dominated convergence) applied to |F_k|^p, p. 90

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace CauchyRiemannIndex

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Dominated convergence in `L^p` for `0 < p < ∞`: if `‖F k‖ ≤ bound` a.e. with `bound ∈ L^p`
and `F k → 0` a.e., then `‖F k‖_{L^p} → 0`. -/
theorem tendsto_eLpNorm_zero_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {F : ℕ → α → E}
    {bound : α → ℝ} (hb : MemLp bound p μ) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0) := by
  sorry

end CauchyRiemannIndex
