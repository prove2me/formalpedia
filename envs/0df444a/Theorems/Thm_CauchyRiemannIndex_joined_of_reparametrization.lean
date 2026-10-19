-- Prove2me | Theorems.Thm_CauchyRiemannIndex_joined_of_reparametrization
-- name    : CauchyRiemannIndex.joined_of_reparametrization
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:56:24.349783+00:00
-- url     : https://prove2.me/theorems/cc502ffa-f554-465a-a0d1-b0e1565baa4d
-- title:
--   Reparametrizing a nondegenerate asymptotic operator does not leave its component
-- statement:
--   Let $S:\mathbb R\to\mathbb R^{2n\times2n}$ be a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $-J_0\partial_t-S$ is nondegenerate, and let $\beta:\mathbb R\to\mathbb R$ be continuously differentiable with
--   $$\beta(0)=0,\qquad \beta(t+1)=\beta(t)+1\quad(t\in\mathbb R).$$
--   Then there is a continuous family $(S_\tau)_{\tau\in[0,1]}$ of continuous $1$-periodic loops of symmetric matrices with $S_0=S$ and $S_1(t)=\beta'(t)\,S(\beta(t))$ such that every $-J_0\partial_t-S_\tau$ is nondegenerate.
--
--   The loop $t\mapsto\beta'(t)S(\beta(t))$ is the time change of $S$ by $\beta$. The statement says that such time changes stay in one path component of the space of nondegenerate asymptotic operators on the trivial bundle (Wendl, Lecture 3, §3.4), so one may replace a loop by a reparametrized one when joining operators of equal Conley–Zehnder index. No monotonicity of $\beta$ is assumed.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The derivative is given as a function `β'` with `HasDerivAt β (β' t) t` for every $t$ and `Continuous β'`. The family is `H : C(unitInterval × ℝ, Mat n)` with `H (0, t) = S t`, `H (1, t) = β' t • S (β t)`, and `IsSymLoop`, `IsNondegenerate` for every slice `fun t => H (τ, t)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Reparametrizing a nondegenerate loop of symmetric matrices by a `C¹` map `β` with
`β 0 = 0` and `β (t + 1) = β t + 1`, as `t ↦ β' t • S (β t)`, stays in the same component of the
space of nondegenerate loops of symmetric matrices. -/
theorem joined_of_reparametrization (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hn : IsNondegenerate S) (β β' : ℝ → ℝ) (hβ : ∀ t, HasDerivAt β (β' t) t)
    (hβ' : Continuous β') (h0 : β 0 = 0) (h1 : ∀ t, β (t + 1) = β t + 1) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧
      (∀ t, H (1, t) = β' t • S (β t)) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  sorry

end CauchyRiemannIndex
