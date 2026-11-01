-- Prove2me | Theorems.Thm_DoublyOptBandit_lemma_2_4
-- name    : DoublyOptBandit.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:26:55.059701+00:00
-- url     : https://prove2.me/theorems/393bcb62-294b-421d-9733-b416faf60531
-- title:
--   Lemma 2.4 — the barrier is flat away from the boundary: $R(x)-R(\bar x)\le\nu\log\frac1{1-\pi_{\bar x}(x)}$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed, convex and compact, $R$ a $\nu$-self-concordant barrier for $X$, and $\bar x\in\operatorname{int}X$ a minimizer of $R$ (a center of $X$). Let $\pi_{\bar x}(y)=\inf\{t>0:\bar x+t^{-1}(y-\bar x)\in X\}$ be the Minkowski function. Then
--
--   1. for every $x\in\operatorname{int}X$,
--   $$
--   R(x)-R(\bar x)\le\nu\log\frac1{1-\pi_{\bar x}(x)};
--   $$
--   2. for every $\varepsilon\in(0,1]$ and every $x\in X_\varepsilon=\{x:\pi_{\bar x}(x)\le\frac1{1+\varepsilon}\}$, $\pi_{\bar x}(x)\le\frac1{1+\varepsilon}$ and $R(x)-R(\bar x)\le\nu\log(1+\frac1\varepsilon)$.
--
--   In the proof of Theorem 3.8 this bounds the initial Bregman divergence $D_{R_i}(p_i,x_i^1)=R_i(p_i)-R_i(x_i^1)$ by $\nu_i\log T$ after moving the equilibrium a distance $O(T^{-1/2})$ away from the boundary.
--
--   Differences from the source:
--   - encoding: R(x) − R(x̄) ≤ ν log(1/(1 − π_x̄(x))) for x (R : int(X) → ℝ) → for x ∈ int X; reason: R is defined on int X only; at x ∈ ∂X, π_x̄(x) = 1 and the right side is +∞
--   - encoding: center x̄ = argmin_{x∈X} R(x) → x̄ ∈ int X minimizing R over int X; reason: R is defined on int X only
--   - encoding: π_x(y) = inf{t ≥ 0 : x + (1/t)(y − x) ∈ X} → infimum over t > 0; reason: 1/t is undefined at t = 0 (in Lean 0⁻¹ = 0 would make π ≡ 0)
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 2.4, p.6 (citing Nesterov and Nemirovski 1994, Propositions 2.3.2 and 2.3.3); Minkowski function, X_ε and center, p.6

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_DoublyOptBandit_LocalNorm

namespace DoublyOptBandit

/-- **Lemma 2.4** (Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4, Lemma 2.4, p.6; citing Nesterov and
Nemirovski 1994, Propositions 2.3.2 and 2.3.3). Let `X ⊆ ℝⁿ` be closed, convex and compact, `R` a
`ν`-self-concordant barrier for `X` and `x̄ = argmin_{x ∈ X} R(x)` a center. Then
`R(x) − R(x̄) ≤ ν log(1/(1 − π_x̄(x)))`; and for every `ε ∈ (0, 1]` and `x ∈ X_ε`,
`π_x̄(x) ≤ 1/(1 + ε)` and `R(x) − R(x̄) ≤ ν log(1 + 1/ε)`.

**Formalization Note** `R : int(X) → ℝ` in the paper, so the first bound is stated for
`x ∈ int X` (at `x ∈ ∂X`, `π_x̄(x) = 1` and the right side is `+∞`); points of `X_ε` lie in `int X`.
The center is a minimizer of `R` over `int X`. The Minkowski function takes its infimum over
`t > 0` (see `minkowski`). -/
theorem lemma_2_4 {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (hXc : IsCompact X)
    (hXcv : Convex ℝ X) (R : EuclideanSpace ℝ (Fin m) → ℝ) (ν : ℝ)
    (hR : EntropicBarrier.Universal.IsNuSelfConcordantBarrier X R ν)
    (xbar : EuclideanSpace ℝ (Fin m)) (hxbar : xbar ∈ interior X)
    (hmin : IsMinOn R (interior X) xbar) :
    (∀ x ∈ interior X, R x - R xbar ≤ ν * Real.log (1 / (1 - minkowski X xbar x))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ scaledSet X xbar ε,
        minkowski X xbar x ≤ 1 / (1 + ε) ∧ R x - R xbar ≤ ν * Real.log (1 + 1 / ε) := by sorry

end DoublyOptBandit
