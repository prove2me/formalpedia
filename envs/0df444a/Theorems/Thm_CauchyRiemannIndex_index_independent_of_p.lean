-- Prove2me | Theorems.Thm_CauchyRiemannIndex_index_independent_of_p
-- name    : CauchyRiemannIndex.index_independent_of_p
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T21:03:26.827635+00:00
-- url     : https://prove2.me/theorems/a7ac8b03-e732-4e0d-ba2a-1c83bc7d08fc
-- title:
--   The kernel and the index of a Cauchy–Riemann operator do not depend on p
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Then for every $p_2\in(1,\infty)$ the kernels of $D_S$ on $W^{1,p}$ and on $W^{1,p_2}$ have the same dimension, and the Fredholm indices of $D_S:W^{1,p}\to L^p$ and $D_S:W^{1,p_2}\to L^{p_2}$ are equal.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. The index is `crIndex`, an integer.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.3, p. 69 (second statement, case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 4.3 (p. 69), second part, case `k = 1`, on the cylinder: if `D_S` is asymptotic
to nondegenerate loops `S±` of symmetric matrices, the kernel dimension and the Fredholm index of
`D_S : W^{1,p} → L^p` do not depend on `p ∈ (1, ∞)`. -/
theorem index_independent_of_p (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (p₂ : ℝ≥0∞) [Fact (1 ≤ p₂)] (hp₂ : 1 < p₂) (hp₂' : p₂ ≠ ⊤) :
    Module.finrank ℝ (crKernel p S) = Module.finrank ℝ (crKernel p₂ S) ∧
      crIndex p S = crIndex p₂ S := by
  sorry

end CauchyRiemannIndex
