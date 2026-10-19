-- Prove2me | Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_homotopy
-- name    : CauchyRiemannIndex.crIndex_eq_of_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T17:20:46.499294+00:00
-- url     : https://prove2.me/theorems/b5e0291e-7278-44ac-844e-61a5f4707474
-- title:
--   The Fredholm index of Cauchy–Riemann operators on the cylinder is constant along continuous families with nondegenerate ends
-- statement:
--   Let $1<p<\infty$ and $n\ge0$. For $\tau\in[0,1]$ let $S_\tau:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous coefficients with $S_\tau(s,\cdot)\to P_\tau$ as $s\to+\infty$ and $S_\tau(s,\cdot)\to M_\tau$ as $s\to-\infty$, uniformly, where $P_\tau,M_\tau$ are continuous loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-P_\tau$ and $-J_0\partial_t-M_\tau$ are nondegenerate. Assume $\tau\mapsto S_\tau$ is continuous in the sup norm: for every $\tau$ and $\varepsilon>0$ there is $\delta>0$ with $|S_\sigma(s,t)_{ij}-S_\tau(s,t)_{ij}|\le\varepsilon$ for all $(s,t)$ and all entries whenever $|\sigma-\tau|<\delta$. Then the Cauchy–Riemann operators $D_{S_\tau}=\partial_s+J_0\partial_t+S_\tau:W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2n})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ satisfy
--   $$\operatorname{ind}D_{S_0}=\operatorname{ind}D_{S_1}.$$
--
--   This is the homotopy invariance of the Fredholm index on the cylinder: the asymptotic loops may move with $\tau$ as long as they stay nondegenerate. It reduces index comparisons to the construction of such families.
--
--   **Formalization Note** The family is `S : unitInterval → ℝ × ℝ → Mat n` with loops `P M : unitInterval → ℝ → Mat n`; each `S τ` satisfies `IsAsymptoticTo (S τ) (P τ) (M τ)` (positive end first), the loops satisfy `IsSymLoop` and `IsNondegenerate`, and the index is `crIndex p` $=\dim\ker D_S-\dim\operatorname{coker}D_S$ from the setting module. No continuity of the loops in $\tau$ is assumed.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103 (cylinder, trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lecture 4–5, homotopy invariance on the cylinder with the trivial bundle and
`1 < p < ∞`: let `τ ↦ S_τ`, `τ ∈ [0, 1]`, be a family of coefficients such that every `S_τ` is
asymptotic to nondegenerate loops `P τ` (at `+∞`) and `M τ` (at `-∞`) of symmetric matrices, and
`τ ↦ S_τ` is continuous uniformly on the cylinder and in all entries. Then
`ind D_{S_0} = ind D_{S_1}`. -/
theorem crIndex_eq_of_homotopy (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (S : unitInterval → ℝ × ℝ → Mat n) (P M : unitInterval → ℝ → Mat n)
    (hP : ∀ τ, IsSymLoop (P τ)) (hM : ∀ τ, IsSymLoop (M τ))
    (hnP : ∀ τ, IsNondegenerate (P τ)) (hnM : ∀ τ, IsNondegenerate (M τ))
    (hS : ∀ τ, IsAsymptoticTo (S τ) (P τ) (M τ))
    (hcont : ∀ τ, ∀ ε > 0, ∃ δ > 0, ∀ σ, dist σ τ < δ → ∀ x i j,
      |S σ x i j - S τ x i j| ≤ ε) :
    crIndex p (S 0) = crIndex p (S 1) := by
  sorry

end CauchyRiemannIndex
