-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_theorem_3_1
-- name    : ChenSimchiLevi.Additive.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:42:40.782242+00:00
-- url     : https://prove2.me/theorems/afeca39b-10e7-4949-8554-a99c392c2bf2
-- title:
--   Theorem 3.1(c)–(d) — additive demand: $g_t(y,d_t(y))$ and $v_t$ are $k$-concave, and an $(s,S,p)$ policy is optimal
-- statement:
--   Consider the finite-horizon joint pricing and inventory model of Chen and Simchi-Levi (2004) with fixed ordering cost $k$, under Assumptions 1–5 (with $c_{T+1} = 0$, $c_t \ge 0$, $k \ge 0$) and additive demand $w_t = D_t(p_t) + \beta_t$. Let $v_t$ be the profit-to-go (2) and $g_t$ the one-period objective (3). Then for every period $t = T, T-1, \dots, 1$:
--
--   **(c)** For every $y$, $g_t(y, \cdot)$ attains its maximum over $[\underline d_t, \bar d_t]$ at some $d_t(y)$, and both
--   $$y \mapsto g_t\big(y, d_t(y)\big) \qquad\text{and}\qquad x \mapsto v_t(x)$$
--   are $k$-concave.
--
--   **(d)** There exist $s_t \le S_t$ such that the following policy is optimal in period $t$: if the initial inventory satisfies $x_t < s_t$, order up to $S_t$ and set the expected demand to $d_t(S_t)$; otherwise order nothing and set the expected demand to $d_t(x_t)$. Precisely, writing $y^*(x) = S_t$ if $x < s_t$ and $y^*(x) = x$ otherwise, for every $x$:
--   1. $y^*(x) \ge x$ and $y^*(x)$ maximizes $-k\,\delta(y - x) + g_t(y, d_t(y))$ over $y \ge x$;
--   2. $v_t(x) = c_t x - k\,\delta(y^*(x) - x) + g_t\big(y^*(x), d_t(y^*(x))\big)$;
--   3. some expected demand $d \in [\underline d_t, \bar d_t]$ maximizes $g_t(y^*(x), \cdot)$; the corresponding price is $p = D_t^{-1}(d)$.
--
--   This is the paper's main result: with additive demand, the $(s, S, p)$ policy conjectured by Thomas (1974) is optimal, and the price depends on the inventory level after ordering.
--
--   **Formalization Note.** $k$-concavity of $f$ is the platform's `BertsekasKConvex k (−f)` (Definition 2.1). The values $g_t(y, d_t(y))$ and $v_t(x)$ are defined as suprema (real `sSup`); the attainment statements in (c) and (d) show that these suprema are maxima. The model is in expected-demand space; the price is $P_t(d) = D_t^{-1}(d)$. The hypotheses $c_{T+1} = 0$, $c_t \ge 0$ and $k \ge 0$ are added to the paper's Assumptions 1–5 (see the model definition).
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, Theorem 3.1(c)–(d)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model

namespace ChenSimchiLevi.Additive

/-- Theorem 3.1(c)–(d) of Chen–Simchi-Levi (2004), p. 890: under additive demand, for every period
`t = T, …, 1`,
(c) `g_t(·, d)` attains its maximum over `[d_t, d̄_t]` at every `y`, and `g_t(y, d_t(y))` and
`v_t(x)` are `k`-concave;
(d) there are `s_t ≤ S_t` such that the `(s, S)` order — order up to `S_t` if `x < s_t`, otherwise
do not order — attains the maximum in (2), `v_t(x)` equals `c_t x` plus that maximum, and the
expected demand is set to a maximizer of `g_t(y, ·)` at the post-order level `y`. -/
theorem theorem_3_1 (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ((∀ y : ℝ, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) ∧
        BertsekasKConvex M.k (fun y => -M.Gstar t y) ∧
        BertsekasKConvex M.k (fun x => -M.v t x)) ∧
      (∃ s S : ℝ, s ≤ S ∧ ∀ x : ℝ,
        x ≤ sSOrder s S x ∧
        (∀ y : ℝ, x ≤ y → M.orderObj t x y ≤ M.orderObj t x (sSOrder s S x)) ∧
        M.v t x = M.c t * x + M.orderObj t x (sSOrder s S x) ∧
        ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t (sSOrder s S x)) (Set.Icc (M.dlo t) (M.dhi t)) d) := by sorry

end ChenSimchiLevi.Additive
