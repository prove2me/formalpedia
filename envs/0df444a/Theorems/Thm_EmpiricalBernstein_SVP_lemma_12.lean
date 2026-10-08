-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_lemma_12
-- name    : EmpiricalBernstein.SVP.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:45.030845+00:00
-- url     : https://prove2.me/theorems/4c3b447c-efc9-41e5-8a3e-7c7c6d831fa8
-- title:
--   Lemma 12 — $\Phi$ and $\Psi$ are Lipschitz in $\|\cdot\|_\infty$ with constants $1+2\sqrt{t/n}$ and $1+6\sqrt{t/n}$
-- statement:
--   Let $n \ge 2$, $t > 0$ and $x, x' \in [0,1]^n$. Then
--
--   $$
--   \text{(i)}\quad \Phi(x,t) - \Phi(x',t) \le \Big(1 + 2\sqrt{t/n}\Big)\, \|x - x'\|_\infty,
--   $$
--
--   $$
--   \text{(ii)}\quad \Psi(x,t) - \Psi(x',t) \le \Big(1 + 6\sqrt{t/n}\Big)\, \|x - x'\|_\infty,
--   $$
--
--   where $\Phi$ and $\Psi$ are the confidence-bound functionals of Section 3 and $\|\cdot\|_\infty$ is the sup norm on $\mathbb R^n$.
--
--   These Lipschitz bounds let a finite sup-norm cover of the function class on the double sample stand in for the whole class in the proof of Theorem 6.
--
--   **Formalization Note** $\|x - x'\|$ is Mathlib's norm on `Fin n → ℝ`, the sup norm. $n \ge 2$ is added, as for every statement involving $\Phi$, $\Psi$ (which contain $n-1$ in a denominator); the page leaves it implicit.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Lemma 12, p. 5

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_PhiPsi

namespace EmpiricalBernstein.SVP

/-- Lemma 12 (arXiv:0907.3740v1, p. 5): Lipschitz properties of `Φ` and `Ψ` in the sup norm
`‖·‖` of `Fin n → ℝ`, for `n ≥ 2`. -/
theorem lemma_12 {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) (x x' : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (hx' : ∀ i, x' i ∈ Set.Icc (0 : ℝ) 1) :
    Phi x t - Phi x' t ≤ (1 + 2 * Real.sqrt (t / n)) * ‖x - x'‖ ∧
      Psi x t - Psi x' t ≤ (1 + 6 * Real.sqrt (t / n)) * ‖x - x'‖ := by sorry

end EmpiricalBernstein.SVP
