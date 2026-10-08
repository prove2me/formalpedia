-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_vt_display
-- name    : ChenSimchiLevi.Additive.vt_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:42:33.117268+00:00
-- url     : https://prove2.me/theorems/1c77c655-d506-4af2-843a-e34ad8a8698f
-- title:
--   Proof of Theorem 3.1, display of $v_t$ — the $(s,S)$ form of $v_t$ and its $k$-concavity
-- statement:
--   Let $k \ge 0$ and $c \in \mathbb R$, and let $G : \mathbb R \to \mathbb R$ be continuous and $k$-concave (that is, $-G$ is $k$-convex in the sense of Definition 2.1), with $G(y) \to -\infty$ as $y \to +\infty$ and as $y \to -\infty$. Define
--   $$W(x) = c\,x + \sup_{y \ge x}\big[-k\,\delta(y - x) + G(y)\big],$$
--   where $\delta(u) = 1$ if $u > 0$ and $0$ otherwise. Then there are $s \le S$ such that
--
--   1. $S$ maximizes $G$;
--   2. $s$ is the smallest $y$ with $G(S) = G(y) + k$;
--   3. $W(x) = -k + G(S) + c\,x$ for $x \le s$, and $W(x) = G(x) + c\,x$ for $x \ge s$;
--   4. $W$ is $k$-concave.
--
--   In the proof of Theorem 3.1 this is applied with $G(y) = g_t(y, d_t(y))$ and $c = c_t$, where $W = v_t$: it gives the $(s_t, S_t)$ form of the profit-to-go and carries $k$-concavity from $g_t(y, d_t(y))$ to $v_t$, closing the induction.
--
--   **Formalization Note.** The statement is model-free. The paper writes $s_t < S_t$; for $k = 0$ one can have $s = S$, so the statement uses $s \le S$.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, §3, proof of Theorem 3.1, display of v_t

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model

open Filter

namespace ChenSimchiLevi.Additive

/-- The display of `v_t` in the proof of Theorem 3.1 of Chen–Simchi-Levi (2004), p. 890, as a
model-free statement: let `G = g_t(·, d_t(·))` be continuous, `k`-concave, with `G(y) → -∞` as
`|y| → ∞`, and let `W(x) = c x + sup_{y ≥ x} [-k δ(y - x) + G(y)]`. Then there are `s ≤ S` such that
`S` maximizes `G`, `s` is the smallest `y` with `G(S) = G(y) + k`,
`W(x) = -k + G(S) + c x` for `x ≤ s` and `W(x) = G(x) + c x` for `x ≥ s`, and `W` is `k`-concave. -/
theorem vt_display (k c : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k) (hGcont : Continuous G)
    (hGtop : Tendsto G atTop atBot) (hGbot : Tendsto G atBot atBot)
    (hGk : BertsekasKConvex k (fun y => -G y)) :
    ∃ s S : ℝ, s ≤ S ∧ IsMaxOn G Set.univ S ∧ IsLeast {y : ℝ | G S = G y + k} s ∧
      (∀ x : ℝ, x ≤ s →
        c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = -k + G S + c * x) ∧
      (∀ x : ℝ, s ≤ x →
        c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = G x + c * x) ∧
      BertsekasKConvex k
        (fun x => -(c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x))) := by sorry

end ChenSimchiLevi.Additive
