-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_late_branch
-- name    : FlexGroupBuy.REE.late_branch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:52.020823+00:00
-- url     : https://prove2.me/theorems/dc0bd7c4-1b39-4028-8e80-f1fd2ef97289
-- title:
--   Proof of Proposition 2, Online Appendix p. 4 — late branch x̄G > x̄G1: closed-form profit, derivative, sign ⩾ 0 iff N ⩽ N̄1
-- statement:
--   Under the standing assumptions and $N\ge1$:
--
--   1. For every $\bar x^G$ with $0<\bar x^G\le N$ and $\bar x^G>\bar x^G_1$,
--   $$
--   \pi^G(\bar x^G)=\frac{\theta L\gamma\lambda N+L(1-\gamma)\lambda(N-\bar x^G)-c\gamma N(\bar x^G-1)}{N-(1-\gamma)\bar x^G}.
--   $$
--   2. The right-hand side, as a function of $\bar x^G$, is differentiable wherever $(1-\gamma)\bar x^G<N$, with derivative
--   $$
--   \frac{\gamma N\,[L(1-\gamma)(\theta-1)\lambda-c(N-1+\gamma)]}{[N-(1-\gamma)\bar x^G]^2}.
--   $$
--   3. At every such point this derivative is nonnegative if and only if $N\le \bar N_1=(\theta-1)(1-\gamma)L\lambda/c+1-\gamma$.
--
--   Hence on the late branch the profit increases to $\bar x^G=N$ when $N\le\bar N_1$ and decreases from $\bar x^G_1$ otherwise.
--
--   **Formalization Note.** Part 1 requires $\bar x^G>0$ because at $\bar x^G=0$ the price is $\bar p^G_2(0)$ by definition.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 4, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 4), late branch `x̄G1 < x ≤ N`: (a) the profit
equals the printed fraction; (b) the fraction has the printed derivative wherever its denominator is
positive; (c) that derivative is nonnegative if and only if `N ≤ N̄1`. -/
theorem late_branch (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    (∀ x : ℝ, 0 < x → x ≤ N → xbar1 P N < x →
      piG P N x = (P.theta * P.L * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * (N - x)
          - P.c * P.gam * N * (x - 1)) / (N - (1 - P.gam) * x)) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      HasDerivAt
        (fun y : ℝ => (P.theta * P.L * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * (N - y)
          - P.c * P.gam * N * (y - 1)) / (N - (1 - P.gam) * y))
        (P.gam * N * (P.L * (1 - P.gam) * (P.theta - 1) * P.lam - P.c * ((N : ℝ) - 1 + P.gam))
          / (N - (1 - P.gam) * x) ^ 2) x) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      (0 ≤ P.gam * N * (P.L * (1 - P.gam) * (P.theta - 1) * P.lam - P.c * ((N : ℝ) - 1 + P.gam))
          / (N - (1 - P.gam) * x) ^ 2 ↔ (N : ℝ) ≤ Nbar1 P)) := by sorry

end FlexGroupBuy.REE
