-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_iff_joined
-- name    : CauchyRiemannIndex.asymptoticCZIndex_eq_iff_joined
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:03:40.56431+00:00
-- url     : https://prove2.me/theorems/3baad947-f741-4703-9aa3-cd85871768bf
-- title:
--   Nondegenerate asymptotic operators with equal Conley–Zehnder index are homotopic through nondegenerate ones
-- statement:
--   Let $S_0$, $S_1$ be continuous loops of symmetric matrices whose asymptotic operators $-J_0\partial_t-S_0$, $-J_0\partial_t-S_1$ are nondegenerate. Then $\mu_{CZ}(-J_0\partial_t-S_0)=\mu_{CZ}(-J_0\partial_t-S_1)$ if and only if there is a continuous family $(S_\tau)_{\tau\in[0,1]}$ of loops of symmetric matrices from $S_0$ to $S_1$ such that every $-J_0\partial_t-S_\tau$ is nondegenerate.
--
--   **Formalization Note** The family is a continuous map `H : C(unitInterval × ℝ, Mat n)` with `IsSymLoop (H (τ, ·))` and `IsNondegenerate (H (τ, ·))` for every $\tau$. Wendl states the theorem for the space of smooth asymptotic operators on a Hermitian bundle with a trivialization; here the bundle is trivial and the loops are continuous.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, Theorem 3.34, p. 62 (trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 3.34 (p. 62), trivial bundle: two nondegenerate loops `S₀`, `S₁` of symmetric
matrices have the same Conley–Zehnder index `μ_CZ(-J₀ ∂ₜ - S)` if and only if they are joined by
a continuous family of nondegenerate loops of symmetric matrices. -/
theorem asymptoticCZIndex_eq_iff_joined (n : ℕ) (S₀ S₁ : ℝ → Mat n) (h₀ : IsSymLoop S₀)
    (h₁ : IsSymLoop S₁) (hn₀ : IsNondegenerate S₀) (hn₁ : IsNondegenerate S₁) :
    asymptoticCZIndex S₀ = asymptoticCZIndex S₁ ↔
      ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S₀ t) ∧ (∀ t, H (1, t) = S₁ t) ∧
        ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  sorry

end CauchyRiemannIndex
