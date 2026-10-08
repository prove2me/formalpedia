-- Prove2me | Theorems.Thm_AMPUniversality_StateEvol_theorem_4
-- name    : AMPUniversality.StateEvol.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:32:20.261995+00:00
-- url     : https://prove2.me/theorems/9bf5e921-4002-4fd6-8543-3982e217f9e9
-- title:
--   Theorem 4 — class averages of AMP iterates converge to Gaussian state evolution
-- statement:
--   Let a polynomial and converging sequence of AMP instances have coordinate classes $C_a^N$, labels $Y(j)$, and Gaussian state-evolution covariance $\Sigma_a^t$. Fix $t\ge1$, a class $a$, and any locally Lipschitz test function $\psi:\mathbb R^q\times\mathbb R^{\tilde q}\to\mathbb R$ for which some $K\ge0$ satisfies $|\psi(x,y)|\le K(1+\|x\|_2^2+\|y\|_2^2)^K$. Then, in probability,
--
--   $$\frac1{|C_a^N|}\sum_{j\in C_a^N}\psi(x_j^t,Y(j))\longrightarrow\mathbb E[\psi(Z_a^t,Y_a)],$$
--
--   where $Z_a^t\sim\mathcal N(0,\Sigma_a^t)$ is independent of $Y_a\sim P_a$. The theorem identifies the limiting class distribution of AMP iterates for polynomial-growth test functions. It also states that the covariance is positive semidefinite and the Gaussian expectation is integrable.
--
--   **Formalization Note** The source display prints $Y(i)$ where the summation index requires $Y(j)$, and omits the superscript $t$ on the covariance in its last line. The squared norms are Euclidean coordinate sums, not Lean's sup norm on function vectors.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 9, Theorem 4, (1.12)

import Definitions.Def_AMPUniversality_StateEvol_SE

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AMPUniversality.StateEvol

/-- Theorem 4: class averages follow the Gaussian state evolution. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (t : ℕ) (ht : 1 ≤ t) (a : Fin k)
    (ψ : (Fin q → ℝ) → EuclideanSpace ℝ (Fin h) → ℝ)
    (hlip : LocallyLipschitz (fun xy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h) =>
      ψ xy.1 xy.2))
    (hgrowth : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y,
      |ψ x y| ≤ K *
        (1 + (∑ s, (y s) ^ 2) + (∑ s, (x s) ^ 2)) ^ K) :
    (M.se t a).PosSemidef ∧
    Integrable (fun zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h) =>
      ψ zy.1 zy.2) ((gaussianVec (M.se t a)).prod (M.Pa a)) ∧
    TendstoInMeasure P
      (fun N ω => ((M.class N a).card : ℝ)⁻¹ *
        ∑ j ∈ M.class N a, ψ (M.orbit N ω t j) (M.Y N ω j))
      atTop
      (fun _ => ∫ zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h),
        ψ zy.1 zy.2 ∂((gaussianVec (M.se t a)).prod (M.Pa a))) := by sorry

end AMPUniversality.StateEvol
