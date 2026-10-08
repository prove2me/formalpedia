-- Prove2me | Theorems.Thm_BoydADMM_Convergence_suboptimality_bound
-- name    : BoydADMM.Convergence.suboptimality_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:11.720833+00:00
-- url     : https://prove2.me/theorems/9e48cf99-8a9b-499c-8e13-a112311a0ab6
-- title:
--   §3.3.1 — if $\|x^k-x^\star\|_2\le d$ then $f(x^k)+g(z^k)-p^\star\le-(y^k)^Tr^k+d\|s^k\|_2\le\|y^k\|_2\|r^k\|_2+d\|s^k\|_2$
-- statement:
--   Under Assumptions 1 and 2, with $\rho>0$, a saddle point $(x^\star,z^\star,y^\star)$ of $L_0$ and any ADMM run, let $k\ge1$ and $d\in\mathbb R$ with $\|x^k-x^\star\|_2\le d$. Then
--
--   $$
--   f(x^k)+g(z^k)-p^\star\le-(y^k)^Tr^k+d\|s^k\|_2\le\|y^k\|_2\|r^k\|_2+d\|s^k\|_2,
--   $$
--
--   where $r^k=Ax^k+Bz^k-c$ and $s^k=\rho A^TB(z^k-z^{k-1})$.
--
--   The middle and right-hand expressions are computable from the iterates once a guess $d$ is fixed, and serve as approximate bounds on the suboptimality in a stopping criterion.
--
--   **Formalization Note** Stated at index $k+1$, $k\ge0$. $p^\star$ is the infimum `optVal`.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), §3.3.1, p. 19

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- §3.3.1, p. 19: if `‖x^k − x⋆‖₂ ≤ d` then
`f(x^k) + g(z^k) − p⋆ ≤ −(y^k)ᵀr^k + d‖s^k‖₂ ≤ ‖y^k‖₂‖r^k‖₂ + d‖s^k‖₂`, for every `k ≥ 1`
(written as `k + 1`, `k ≥ 0`). -/
theorem suboptimality_bound
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) (d : ℝ) (hd : ‖x (k + 1) - xs‖ ≤ d) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
        -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ ∧
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ ≤
        ‖y (k + 1)‖ * ‖P.resid (x (k + 1)) (z (k + 1))‖
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ := by sorry

end BoydADMM.Convergence
