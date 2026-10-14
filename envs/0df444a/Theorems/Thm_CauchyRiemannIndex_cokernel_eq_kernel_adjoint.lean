-- Prove2me | Theorems.Thm_CauchyRiemannIndex_cokernel_eq_kernel_adjoint
-- name    : CauchyRiemannIndex.cokernel_eq_kernel_adjoint
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:02:49.526477+00:00
-- url     : https://prove2.me/theorems/f9c081e7-ba16-4bac-b408-351cc1b3fecf
-- title:
--   The cokernel of a Cauchy–Riemann operator is the kernel of its conjugated formal adjoint
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Let $1/p+1/q=1$, let $C$ be complex conjugation on $\mathbb{C}^n=\mathbb{R}^{2n}$ and $\bar S(s,t)=-C\,S(s,t)^{\mathsf T}C$. Then the cokernel $L^p/\operatorname{im}(D_S:W^{1,p}\to L^p)$ is finite-dimensional, and
--   $$\dim\operatorname{coker}\big(D_S:W^{1,p}\to L^p\big)=\dim\ker\big(D_{\bar S}:W^{1,q}\to L^q\big).$$
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. $C$ is `conjMat n`; $q$ is in `ℝ≥0∞` with `Fact (1 ≤ q)` and `1 / p + 1 / q = 1`. $D_{\bar S}=-C\,D_S^*\,C$, where $D_S^*$ is the formal adjoint of $D_S$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Lemma 4.17, Proposition 4.18 and Theorem 4.20, pp. 76–79

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 4.17, Proposition 4.18 and Theorem 4.20 (pp. 76–79), on the cylinder: let `D_S`
be asymptotic to nondegenerate loops `S±` of symmetric matrices, `1 < p < ∞` and
`1/p + 1/q = 1`. The cokernel of `D_S : W^{1,p} → L^p` is finite-dimensional, and its dimension
is that of the kernel of the conjugated formal adjoint `D_{S̄} : W^{1,q} → L^q`,
`S̄(s, t) = -C S(s, t)ᵀ C`, where `C` is complex conjugation on `ℂⁿ = ℝ²ⁿ`. -/
theorem cokernel_eq_kernel_adjoint (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hpq : 1 / p + 1 / q = 1) :
    FiniteDimensional ℝ (LpCyl n p ⧸ crRange p S) ∧
      Module.finrank ℝ (LpCyl n p ⧸ crRange p S) =
        Module.finrank ℝ (crKernel q (fun x => -(conjMat n * (S x)ᵀ * conjMat n))) := by
  sorry

end CauchyRiemannIndex
