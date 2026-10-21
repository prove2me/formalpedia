-- Prove2me | Theorems.Thm_BuyXFree_Threshold_proposition_2
-- name    : BuyXFree.Threshold.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:28.784988+00:00
-- url     : https://prove2.me/theorems/c8c315e3-1c09-43bb-b59c-efff411bf67d
-- title:
--   Proposition 2(a)–(d), p. 10 (with Lemmas 6–9(a)) — the four price ranges and the purchase/redemption rule
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Assume moreover $\lambda>0$ and $q>0$. $J$ denotes any solution of the optimality equations (1)–(2) of the consumer facing price $p$ and threshold $X$. With the boundary prices $p^D(\tau)$, $p^B(\tau)$ of p. 10:
--
--   1. **(a)** if $p\le p^D(0)$, the consumer buys in every state $x<X$ and redeems in state $X$, under either outside option;
--   2. **(b)** if $p^D(\tau-1)<p\le\min\{p^B(\tau),p^D(\tau)\}$ for a threshold $\tau\in\{1,\dots,X-1\}$, then facing $\bar v$ she does not buy in states $0,\dots,\tau-1$, buys in states $\tau,\dots,X-1$, and redeems in state $X$;
--   3. **(c)** if $p^D(X-1)<p\le\min\{p^B(X),p^D(X)\}$, then facing $\bar v$ she buys in no state but redeems in state $X$;
--   4. **(d)** if $p^D(X)<p\le\dfrac{(1-A^{X+1})v+A^X(1-A)k}{1-A^X}$, then facing $\bar v$ she neither buys nor redeems in any state.
--
--   In parts (b)–(d), facing the outside option $0$ she buys in every state $x<X$ and redeems in state $X$ (part (a) of Lemmas 7–9, pp. 40–42).
--   $$\text{price range}\ \Longrightarrow\ \text{purchase/redemption rule}.$$
--
--   This is the paper's characterization of the consumer's response to a program $(p,X)$. For $X=1$ part (b) is empty.
--
--   **Formalization Note** The hypotheses $\lambda>0$, $q>0$ (equivalently $A>0$) are added: $p^B(X)$ and $p^D(X)$ divide by quantities that vanish when $A=0$, and with Lean's convention $x/0=0$ part (d) would be false at $\lambda=0$. Each part also records the outside-option-$0$ behaviour of Lemmas 6–9(a).
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 10, Proposition 2; pp. 39–42, Lemmas 6–9 part (a)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proposition 2, p. 10, with the outside-option-`0` behaviour of parts (a) of Lemmas 6–9
(pp. 39–42): the four price ranges and the decisions they induce. Added hypothesis: `λ > 0`,
`q > 0` (so `A > 0`; the bounds `p^B(X)`, `p^D(X)` divide by terms that vanish at `A = 0`). -/
theorem proposition_2 (P : Params) (hP : P.Standing) (hlam : 0 < P.lam) (hq : 0 < P.q)
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    -- (a)
    (p ≤ pD P X 0 →
      (∀ x < X, BuysHigh P p J x) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (b)
    (∀ τ : ℕ, 1 ≤ τ → τ + 1 ≤ X → pD P X (τ - 1) < p → p ≤ min (pB P X τ) (pD P X τ) →
      (∀ x < X, (BuysHigh P p J x ↔ τ ≤ x)) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (c)
    (pD P X (X - 1) < p → p ≤ min (pB P X X) (pD P X X) →
      (∀ x < X, ¬ BuysHigh P p J x) ∧ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) ∧
    -- (d)
    (pD P X X < p → p ≤ pdUpper P X →
      (∀ x < X, ¬ BuysHigh P p J x) ∧ ¬ RedeemsHigh P X J ∧
        (∀ x < X, BuysLow P p J x) ∧ RedeemsLow P X J) := by sorry
end BuyXFree.Threshold
