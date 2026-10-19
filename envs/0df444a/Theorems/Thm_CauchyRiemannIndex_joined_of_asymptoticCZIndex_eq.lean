-- Prove2me | Theorems.Thm_CauchyRiemannIndex_joined_of_asymptoticCZIndex_eq
-- name    : CauchyRiemannIndex.joined_of_asymptoticCZIndex_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:51.842581+00:00
-- url     : https://prove2.me/theorems/25a1aa0a-01b7-426d-ad05-521f635ca3d5
-- title:
--   Nondegenerate asymptotic operators with the same Conley–Zehnder index are joined through nondegenerate ones
-- statement:
--   Let $S_0,S_1:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous $1$-periodic loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-S_0$ and $-J_0\partial_t-S_1$ are nondegenerate, and suppose
--   $$\mu_{CZ}(-J_0\partial_t-S_0)=\mu_{CZ}(-J_0\partial_t-S_1).$$
--   Then there is a continuous family $(S_\tau)_{\tau\in[0,1]}$ of continuous $1$-periodic loops of symmetric matrices from $S_0$ to $S_1$ such that every $-J_0\partial_t-S_\tau$ is nondegenerate.
--
--   This is the "if" half of the classification of nondegenerate asymptotic operators by their Conley–Zehnder index (Wendl, Theorem 3.34, trivial bundle): each value of the index is attained on a single path component of the space of nondegenerate asymptotic operators.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The family is a continuous map `H : C(unitInterval × ℝ, Mat n)` (joint continuity in $(\tau,t)\in[0,1]\times\mathbb R$) with `H (0, t) = S₀ t`, `H (1, t) = S₁ t`, and, for every $\tau$, `IsSymLoop (fun t => H (τ, t))` and `IsNondegenerate (fun t => H (τ, t))`. Wendl states the theorem for smooth asymptotic operators on a Hermitian bundle with a trivialization; here the bundle is trivial and the loops are continuous.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 3.34 (p. 62), trivial bundle, other direction: two nondegenerate loops of
symmetric matrices with the same Conley–Zehnder index are joined by a continuous family of
nondegenerate loops of symmetric matrices. -/
theorem joined_of_asymptoticCZIndex_eq (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁)
    (h : asymptoticCZIndex S₀ = asymptoticCZIndex S₁) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  sorry

end CauchyRiemannIndex
