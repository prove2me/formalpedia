-- Prove2me | Theorems.Thm_DRJointCC_Individual_lemma_2_1
-- name    : DRJointCC.Individual.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:56.708713+00:00
-- url     : https://prove2.me/theorems/f6ccf7b8-8a05-4e20-ad87-f7acf58a8da1
-- title:
--   Lemma 2.1 (Farkas Lemma), pp. 7–8 — nonlinear Farkas lemma for convex functions under Slater
-- statement:
--   Let $f_0,\dots,f_p:\mathbb R^k\to\mathbb R$ be convex functions, and assume that there is a strictly feasible point $\bar\xi$ with $f_i(\bar\xi)<0$ for $i=1,\dots,p$. Then $f_0(\xi)\ge0$ for all $\xi$ with $f_i(\xi)\le0$, $i=1,\dots,p$, if and only if there exist constants $\tau_i\ge0$ such that
--
--   $$
--   f_0(\xi)+\sum_{i=1}^p\tau_if_i(\xi)\ge0\qquad\forall\xi\in\mathbb R^k.
--   $$
--
--   This is the nonlinear Farkas lemma. In the proof of Theorem 2.2 it converts the semi-infinite constraint of the worst-case probability problem into a single inequality with a multiplier when the loss is concave.
--
--   **Formalization Note** The constraints $i=1,\dots,p$ are indexed by `Fin p` (indices shifted by one). The lemma involves no probability distribution, so the standing assumptions of §2 are not hypotheses here.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, pp. 7–8, Lemma 2.1

import Mathlib

namespace DRJointCC.Individual

/-- Lemma 2.1 (Farkas Lemma), pp. 7–8: for convex `f₀, …, f_p : ℝ^k → ℝ` with a strictly
feasible point, `f₀ ≥ 0` on `{f_i ≤ 0 ∀ i}` iff some `τ ≥ 0` gives
`f₀ + ∑ τ_i f_i ≥ 0` on all of `ℝ^k`. The constraints `i = 1, …, p` are indexed by `Fin p`. -/
theorem lemma_2_1 {k p : ℕ} (f0 : (Fin k → ℝ) → ℝ) (f : Fin p → (Fin k → ℝ) → ℝ)
    (hf0 : ConvexOn ℝ Set.univ f0) (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hslater : ∃ ξbar : Fin k → ℝ, ∀ i, f i ξbar < 0) :
    (∀ ξ, (∀ i, f i ξ ≤ 0) → 0 ≤ f0 ξ) ↔
      ∃ τ : Fin p → ℝ, (∀ i, 0 ≤ τ i) ∧ ∀ ξ, 0 ≤ f0 ξ + ∑ i, τ i * f i ξ := by sorry

end DRJointCC.Individual
