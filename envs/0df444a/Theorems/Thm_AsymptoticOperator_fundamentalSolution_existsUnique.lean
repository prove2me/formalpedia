-- Prove2me | Theorems.Thm_AsymptoticOperator_fundamentalSolution_existsUnique
-- name    : AsymptoticOperator.fundamentalSolution_existsUnique
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:34:18.845461+00:00
-- url     : https://prove2.me/theorems/833f4006-586e-48d2-89ef-99d4d75ebf10
-- title:
--   Existence and uniqueness of the fundamental solution $\Psi' = J_0 S \Psi$
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous. There is exactly one map $\Psi:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ with $\Psi(0)=\mathrm{Id}$ that is differentiable everywhere with
--   $$\Psi'(t)=J_0\,S(t)\,\Psi(t)\qquad(t\in\mathbb{R}),$$
--   where $S$ is viewed as a $1$-periodic function on $\mathbb{R}$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.4, p. 61 (informal there)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Every continuous loop `S` has exactly one fundamental solution `Ψ`:
`Ψ(0) = Id`, `Ψ' = J₀ S Ψ` on `ℝ`. -/
theorem fundamentalSolution_existsUnique {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃! Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ := by sorry

end AsymptoticOperator
