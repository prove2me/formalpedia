-- Prove2me | Theorems.Thm_AsymptoticOperator_fundamentalSolution_symplectic
-- name    : AsymptoticOperator.fundamentalSolution_symplectic
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:34:34.186135+00:00
-- url     : https://prove2.me/theorems/23c1826b-0310-4706-a473-f150e5e2770b
-- title:
--   The fundamental solution of a symmetric loop is symplectic
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$, and let $\Psi$ be its fundamental solution. Then $\Psi(t)\in\mathrm{Sp}(2n)$, i.e. $\Psi(t)J_0\Psi(t)^{\mathsf T}=J_0$, for every $t\in\mathbb{R}$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, p. 61 (informal there)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.4, p. 61: for a loop of symmetric matrices the fundamental solution is a path
in `Sp(2n)` starting at `Id`. -/
theorem fundamentalSolution_symplectic {n : ℕ} (S : C(UnitAddCircle, Mat n))
    (hS : IsSymLoop S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (t : ℝ) :
    IsSymplectic (Ψ t) := by sorry

end AsymptoticOperator
