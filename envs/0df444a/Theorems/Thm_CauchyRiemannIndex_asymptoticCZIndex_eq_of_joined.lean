-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_of_joined
-- name    : CauchyRiemannIndex.asymptoticCZIndex_eq_of_joined
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:50.322611+00:00
-- url     : https://prove2.me/theorems/aace8165-9bd2-469e-81ef-be149c429bed
-- title:
--   Loops joined through nondegenerate asymptotic operators have the same Conley–Zehnder index
-- statement:
--   Let $(S_\tau)_{\tau\in[0,1]}$ be a continuous family of continuous $1$-periodic loops $S_\tau:\mathbb R\to\mathbb R^{2n\times2n}$ of symmetric matrices such that every asymptotic operator $-J_0\partial_t-S_\tau$ is nondegenerate. Then
--   $$\mu_{CZ}(-J_0\partial_t-S_0)=\mu_{CZ}(-J_0\partial_t-S_1).$$
--
--   This is the "only if" half of the classification of nondegenerate asymptotic operators by their Conley–Zehnder index (Wendl, Theorem 3.34, trivial bundle): the index is constant on path components of the space of nondegenerate asymptotic operators.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The family is a continuous map `H : C(unitInterval × ℝ, Mat n)` with `H (0, t) = S₀ t`, `H (1, t) = S₁ t`, and, for every $\tau$, `IsSymLoop (fun t => H (τ, t))` and `IsNondegenerate (fun t => H (τ, t))`. The index is `asymptoticCZIndex`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 3.34 (p. 62), trivial bundle, one direction: two loops of symmetric matrices
joined by a continuous family of nondegenerate loops of symmetric matrices have the same
Conley–Zehnder index. -/
theorem asymptoticCZIndex_eq_of_joined (n : ℕ) (S₀ S₁ : ℝ → Mat n)
    (H : C(unitInterval × ℝ, Mat n)) (hH₀ : ∀ t, H (0, t) = S₀ t) (hH₁ : ∀ t, H (1, t) = S₁ t)
    (hH : ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t))) :
    asymptoticCZIndex S₀ = asymptoticCZIndex S₁ := by
  sorry

end CauchyRiemannIndex
