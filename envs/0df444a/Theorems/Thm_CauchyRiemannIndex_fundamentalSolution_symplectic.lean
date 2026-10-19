-- Prove2me | Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
-- name    : CauchyRiemannIndex.fundamentalSolution_symplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:47.276237+00:00
-- url     : https://prove2.me/theorems/b65759e3-2042-4f58-9cf8-069e8ba5c43c
-- title:
--   The fundamental solution of a family of symmetric matrices is symplectic
-- statement:
--   Let $S:\mathbb R\to\mathbb R^{2n\times2n}$ with $S(t)$ symmetric for every $t$, and let $\Psi:\mathbb R\to\mathbb R^{2n\times2n}$ satisfy $\Psi(0)=\mathrm{Id}$ and $\Psi'(t)=J_0S(t)\Psi(t)$ for all $t$, where $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$. Then
--   $$\Psi(t)\in\mathrm{Sp}(2n,\mathbb R)\qquad\text{for every }t\in\mathbb R.$$
--
--   For a loop of symmetric matrices this says that the fundamental solution of the asymptotic operator $-J_0\partial_t-S$ is a path of symplectic matrices starting at the identity (Wendl, Lecture 3, §3.4, p. 61), which is the input of the Conley–Zehnder index.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. Symmetry is `(S t).IsSymm`; no continuity of $S$ is assumed. The hypothesis on $\Psi$ is `IsFundamentalSolution S Ψ`, and the conclusion is `IsSymplectic (Ψ t)`, i.e. membership in Mathlib's `Matrix.symplecticGroup`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl §3.4, p. 61: if `S(t)` is symmetric for every `t`, the fundamental solution of `S`
takes values in the symplectic group. -/
theorem fundamentalSolution_symplectic (n : ℕ) (S : ℝ → Mat n) (hS : ∀ t, (S t).IsSymm)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (t : ℝ) : IsSymplectic (Ψ t) := by
  sorry

end CauchyRiemannIndex
