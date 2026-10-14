-- Prove2me | Theorems.Thm_CauchyRiemannIndex_index_formula
-- name    : CauchyRiemannIndex.index_formula
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:05:31.896891+00:00
-- url     : https://prove2.me/theorems/5fa86b03-0823-4686-b233-30bb0a191490
-- title:
--   The index formula for Cauchy–Riemann operators on the cylinder
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Then $D_S:W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2n})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ is Fredholm and
--   $$\operatorname{ind}D_S=\mu_{CZ}(A^+)-\mu_{CZ}(A^-).$$
--
--   This is Wendl's Riemann–Roch formula with punctures, $\operatorname{ind}D=n\chi(\dot\Sigma)+2c_1^\tau(E)+\sum_{z\in\Gamma^+}\mu_{CZ}^\tau(A_z)-\sum_{z\in\Gamma^-}\mu_{CZ}^\tau(A_z)$, for the cylinder $\dot\Sigma=\mathbb{R}\times S^1$ (the sphere with one positive puncture at $s=+\infty$ and one negative puncture at $s=-\infty$), where $\chi(\dot\Sigma)=0$ and $c_1^\tau(E)=0$ for the global trivialization of $E=\dot\Sigma\times\mathbb{C}^n$. It is the dimension formula for moduli spaces of Floer trajectories and of holomorphic cylinders in symplectizations.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. "Fredholm" is `IsFredholmCR p S` (finite-dimensional kernel, closed range, finite-dimensional cokernel), and the index is `crIndex p S` $=\dim\ker-\dim(L^p/\operatorname{im})$. $\mu_{CZ}(A^\pm)$ is `asymptoticCZIndex S±`, the Conley–Zehnder index of the path $\Psi|_{[0,1]}$ of the fundamental solution of $\Psi'=J_0S^\pm\Psi$. Wendl's operators have smooth coefficients converging in $C^\infty$; here $S$ is only continuous, with uniform convergence at the ends (Remark 4.4).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Theorem 5.4, p. 82, with Lecture 4, Theorem 4.3, p. 69 (cylinder, trivial bundle, k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 5.4 (p. 82) with Theorem 4.3 (p. 69), for the cylinder `ℝ × S¹` (one positive
puncture at `s = +∞`, one negative puncture at `s = -∞`) and the trivial bundle with its global
trivialization: if `D_S = ∂ₛ + J₀ ∂ₜ + S(s, t)` is asymptotic to nondegenerate loops `S±` of
symmetric matrices and `1 < p < ∞`, then `D_S : W^{1,p} → L^p` is Fredholm and
`ind D_S = μ_CZ(-J₀ ∂ₜ - S⁺) - μ_CZ(-J₀ ∂ₜ - S⁻)`. -/
theorem index_formula (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    IsFredholmCR p S ∧ crIndex p S = asymptoticCZIndex Splus - asymptoticCZIndex Sminus := by
  sorry

end CauchyRiemannIndex
