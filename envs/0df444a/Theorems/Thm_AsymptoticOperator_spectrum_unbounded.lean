-- Prove2me | Theorems.Thm_AsymptoticOperator_spectrum_unbounded
-- name    : AsymptoticOperator.spectrum_unbounded
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:33:22.609429+00:00
-- url     : https://prove2.me/theorems/045d852d-8662-4329-a12c-1b794cb909db
-- title:
--   The spectrum of an asymptotic operator is unbounded in both directions
-- statement:
--   Let $n\ge1$ and let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$. For every $c\in\mathbb{R}$, $A_S$ has an eigenvalue $\mu>c$ and an eigenvalue $\mu<-c$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, Proposition 3.28, p. 61

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.4, Proposition 3.28: for `n ≥ 1`, `A_S` has eigenvalues of both signs of
arbitrarily large absolute value. -/
theorem spectrum_unbounded {n : ℕ} (hn : 0 < n) (S : C(UnitAddCircle, Mat n))
    (hS : IsSymLoop S) (c : ℝ) :
    (∃ μ : ℝ, c < μ ∧ eigenspace (asymptoticOperator S) μ ≠ ⊥) ∧
      ∃ μ : ℝ, μ < -c ∧ eigenspace (asymptoticOperator S) μ ≠ ⊥ := by sorry

end AsymptoticOperator
