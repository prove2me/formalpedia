-- Prove2me | Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
-- name    : CauchyRiemannIndex.fundamentalSolution_existsUnique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:43.831043+00:00
-- url     : https://prove2.me/theorems/2d81cc27-100b-4100-9be4-c96a7908fd14
-- title:
--   Existence and uniqueness of the fundamental solution of $\Psi'=J_0S\Psi$
-- statement:
--   Let $n\ge0$, let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}\in\mathbb R^{2n\times2n}$, and let $S:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous. Then there is exactly one map $\Psi:\mathbb R\to\mathbb R^{2n\times2n}$ such that
--   $$\Psi(0)=\mathrm{Id},\qquad \Psi'(t)=J_0S(t)\Psi(t)\quad\text{for all }t\in\mathbb R.$$
--
--   This is the fundamental solution through which nondegeneracy and the Conley–Zehnder index of the asymptotic operator $-J_0\partial_t-S$ are defined (Wendl, Lecture 3, §3.4).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The two conditions are `IsFundamentalSolution S Ψ` (with `HasDerivAt` at every real $t$). $S$ is only assumed continuous: neither periodicity nor symmetry is required.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Every continuous `S : ℝ → Mat n` has exactly one fundamental solution `Ψ`:
`Ψ(0) = Id` and `Ψ' = J₀ S Ψ` on `ℝ`. -/
theorem fundamentalSolution_existsUnique (n : ℕ) (S : ℝ → Mat n) (hS : Continuous S) :
    ∃! Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ := by
  sorry

end CauchyRiemannIndex
