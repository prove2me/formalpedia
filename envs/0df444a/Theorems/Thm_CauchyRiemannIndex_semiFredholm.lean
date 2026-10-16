-- Prove2me | Theorems.Thm_CauchyRiemannIndex_semiFredholm
-- name    : CauchyRiemannIndex.semiFredholm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:02:32.745097+00:00
-- url     : https://prove2.me/theorems/8ba5b34d-cc0c-46cf-9e2b-03a9170e4568
-- title:
--   Cauchy–Riemann operators with nondegenerate asymptotics are semi-Fredholm
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Then $D_S:W^{1,p}\to L^p$ has finite-dimensional kernel and closed range.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Corollary 4.14, p. 74 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Corollary 4.14 (p. 74), case `k = 1`: if `D_S` is asymptotic to nondegenerate loops
`S±` of symmetric matrices and `1 < p < ∞`, then `D_S : W^{1,p} → L^p` is semi-Fredholm: its
kernel is finite-dimensional and its range is closed. -/
theorem semiFredholm (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    FiniteDimensional ℝ (crKernel p S) ∧ IsClosed (crRange p S : Set (LpCyl n p)) := by
  sorry

end CauchyRiemannIndex
