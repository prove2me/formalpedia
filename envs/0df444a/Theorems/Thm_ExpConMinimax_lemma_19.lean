-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_19
-- name    : ExpConMinimax.lemma_19
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:50:41.606085+00:00
-- url     : https://prove2.me/theorems/0cfcecc3-6fe9-4ec3-80c7-a1b5a71ca851
-- title:
--   Lemma 19 — $f(x)-f(x^*)\ge-\|\gamma^*\|\,\|g(x)_+\|$ at a Lagrangian saddle point
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$, $f:\mathbb R^n\to\mathbb R$ and $g:\mathbb R^n\to\mathbb R^m$, and let $(x^*,\gamma^*)\in\mathcal X\times\mathbb R^m_+$ be a saddle point of the Lagrangian $\mathcal L(x;\gamma)=f(x)+\gamma^\top g(x)$ of the problem $\min_{x\in\mathcal X}\{f(x)\mid g(x)\le0\}$:
--   $$\mathcal L(x^*;\gamma)\le\mathcal L(x^*;\gamma^*)\le\mathcal L(x;\gamma^*)\qquad\text{for all }(x,\gamma)\in\mathcal X\times\mathbb R^m_+ .$$
--   Then for every $x\in\mathcal X$,
--   $$f(x)-f(x^*)\ \ge\ -\|\gamma^*\|\,\|g(x)_+\| .$$
--
--   An infeasible point can beat the optimal value only by an amount proportional to its constraint violation; Lemma 1 applies this to both players of the minimax problem.
--
--   Differences from the source:
--   - generalization: $f$, $g_i$ closed proper convex and $\mathcal X$ nonempty closed convex → no convexity, closedness or nonemptiness assumed; reason: the proof uses only the saddle inequalities; every instance of the paper is an instance
--   - encoding: $f$, $g_i$ closed proper convex functions (possibly extended-valued) → $f$, $g$ real-valued on $\mathbb R^n$; reason: extended values only add cases where the bound is trivial or undefined
--   - encoding: saddle point with $\mathcal L(x^*;\gamma)\le\mathcal L(x^*;\gamma^*)=f(x^*)\le\mathcal L(x;\gamma^*)$ → the two saddle inequalities only; reason: the middle identity follows from them (take $\gamma=0$ and $\gamma=2\gamma^*$)
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 19, p.26

import Mathlib
import Definitions.Def_ExpConMinimax_Vec

namespace ExpConMinimax

/-- **Lemma 19** (Lagrangian lower bound for a constrained problem).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 19, p.26:

"Let `(x*,γ*) ∈ ℝⁿ × ℝᵐ_+` be a saddle point to the following convex optimization problem
`min_{x∈X} {f(x) | g(x) ≤ 0}` (A.1), where `f` and `gᵢ, i = 1,…,m` are closed proper convex
functions and `X ⊆ ℝⁿ` is a nonempty closed convex set. Then, it holds for all `x ∈ X` that
`f(x) − f(x*) ≥ −‖γ*‖‖g(x)₊‖`."

The saddle point is that of the Lagrangian `𝓛(x;γ) = f(x) + γᵀg(x)` on `X × ℝᵐ_+` (proof of
Lemma 19, p.26): `𝓛(x*;γ) ≤ 𝓛(x*;γ*) ≤ 𝓛(x;γ*)` for all `(x,γ) ∈ X × ℝᵐ_+`.

**Formalization Note.** `f` and `g` are real/vector valued. The convexity and closedness of
`f`, `gᵢ`, `X` are not assumed: the statement holds for every saddle point of the Lagrangian.
The identity `𝓛(x*;γ*) = f(x*)` used in the proof follows from the two saddle inequalities
and is not assumed. -/
theorem lemma_19 {n m : ℕ} (X : Set (Vec n)) (f : Vec n → ℝ) (g : Vec n → Vec m)
    (xs : Vec n) (γs : Vec m) (hxs : xs ∈ X) (hγs : IsNonneg γs)
    (hsaddle : ∀ x ∈ X, ∀ γ : Vec m, IsNonneg γ →
      f xs + inner ℝ γ (g xs) ≤ f xs + inner ℝ γs (g xs) ∧
      f xs + inner ℝ γs (g xs) ≤ f x + inner ℝ γs (g x)) :
    ∀ x ∈ X, -(‖γs‖ * ‖vecPosPart (g x)‖) ≤ f x - f xs := by sorry

end ExpConMinimax
