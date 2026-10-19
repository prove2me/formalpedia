-- Prove2me | Theorems.Thm_CauchyRiemannIndex_joined_of_symplecticPath_family
-- name    : CauchyRiemannIndex.joined_of_symplecticPath_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:51:28.546712+00:00
-- url     : https://prove2.me/theorems/ab702e78-f680-4bd5-b3fa-1fbee41cba11
-- title:
--   A family of fundamental-solution paths in $SP(n)$ yields a family of nondegenerate asymptotic operators
-- statement:
--   Let $S_0,S_1:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous $1$-periodic loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-S_0$ and $-J_0\partial_t-S_1$ are nondegenerate, and let $\Psi_0,\Psi_1$ be their fundamental solutions: $\Psi_i(0)=\mathrm{Id}$ and $\Psi_i'=J_0S_i\Psi_i$ on $\mathbb R$. Suppose there is a continuous map $G:[0,1]\times[0,1]\to\mathbb R^{2n\times2n}$ with
--   $$G(0,t)=\Psi_0(t),\qquad G(1,t)=\Psi_1(t)\qquad(t\in[0,1]),$$
--   such that for every $s\in[0,1]$ the path $G(s,\cdot)$ takes values in $\mathrm{Sp}(2n,\mathbb R)$, starts at $\mathrm{Id}$, and $1$ is not an eigenvalue of $G(s,1)$. Then there is a continuous family $(S_\tau)_{\tau\in[0,1]}$ of continuous $1$-periodic loops of symmetric matrices from $S_0$ to $S_1$ such that every $-J_0\partial_t-S_\tau$ is nondegenerate.
--
--   This passes from the classification of paths in $SP(n)$ to the classification of nondegenerate asymptotic operators on the trivial bundle (Wendl, Theorem 3.34): a joining of the time-$[0,1]$ fundamental-solution paths through nondegenerate symplectic arcs produces a joining of the operators through nondegenerate ones.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The loops satisfy `IsSymLoop` and `IsNondegenerate`, and the fundamental solutions `IsFundamentalSolution S₀ Ψ₀`, `IsFundamentalSolution S₁ Ψ₁`. The given family is `G : C(unitInterval × unitInterval, Mat n)` with `G (0, t) = Ψ₀ t`, `G (1, t) = Ψ₁ t`, `IsSymplectic (G (s, t))`, `G (s, 0) = 1` and `(1 - G (s, 1)).det ≠ 0`. The conclusion has the same form as Theorem 3.34: a continuous `H : C(unitInterval × ℝ, Mat n)` with `H (0, t) = S₀ t`, `H (1, t) = S₁ t`, and `IsSymLoop`, `IsNondegenerate` for every slice `fun t => H (τ, t)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- If the fundamental solutions of two nondegenerate loops of symmetric matrices, restricted to
`[0, 1]`, are joined by a continuous family of paths in `SP(n)`, then the two loops are joined by
a continuous family of nondegenerate loops of symmetric matrices. -/
theorem joined_of_symplecticPath_family (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁)
    (Ψ₀ Ψ₁ : ℝ → Mat n) (hΨ₀ : IsFundamentalSolution S₀ Ψ₀) (hΨ₁ : IsFundamentalSolution S₁ Ψ₁)
    (G : C(unitInterval × unitInterval, Mat n)) (hG₀ : ∀ t : unitInterval, G (0, t) = Ψ₀ t)
    (hG₁ : ∀ t : unitInterval, G (1, t) = Ψ₁ t) (hGs : ∀ s t, IsSymplectic (G (s, t)))
    (hG0 : ∀ s, G (s, 0) = 1) (hG1 : ∀ s, (1 - G (s, 1)).det ≠ 0) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  sorry

end CauchyRiemannIndex
