-- Prove2me | Theorems.Thm_BuyXFree_Threshold_lemma_1
-- name    : BuyXFree.Threshold.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:35.343989+00:00
-- url     : https://prove2.me/theorems/728c9f93-0c51-49d2-90e1-378d2e0c5bd2
-- title:
--   Lemma 1, p. 12 — case (b) stationary probabilities and demand λqX/(τ + q(X − τ + 1))
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Let $1\le\tau\le X-1$ and suppose the consumer's decisions follow case (b) with threshold $\tau$: at outside option $0$ she buys in every state $x<X$, at outside option $\bar v$ she buys exactly in the states $\tau\le x<X$, and she redeems in state $X$ under either outside option. Then the vector
--   $$q_i=\frac{1}{\tau+q(X-\tau+1)}\ (i=0,\dots,\tau-1),\qquad q_i=\frac{q}{\tau+q(X-\tau+1)}\ (i=\tau,\dots,X)$$
--   is a stationary distribution of the induced point-inventory chain; when $\lambda>0$ and $q>0$ it is the only one; and the purchase probability under it is
--   $$\lambda\Bigl(q\sum_{i=0}^{\tau-1}q_i+\sum_{i=\tau}^{X-1}q_i\Bigr)=\frac{\lambda qX}{\tau+q(X-\tau+1)}.$$
--
--   This gives the firm's demand in case (b), the objective of problem (4).
--
--   **Formalization Note** No value function is involved: the statement is about the chain induced by the case (b) decisions. Uniqueness is asserted under $\lambda>0$, $q>0$, where the chain is irreducible; at $\lambda=0$ or $q=0$ other stationary laws exist.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 12, Lemma 1 (proof p. 42)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Definitions.Def_MarkovChain

namespace BuyXFree.Threshold

open Matrix

/-- Lemma 1, p. 12: under the case (b) behaviour with threshold `1 ≤ τ ≤ X − 1`, the vector
`q_i = 1/(τ + q(X − τ + 1))` (`i < τ`), `q_i = q/(τ + q(X − τ + 1))` (`τ ≤ i ≤ X`) is a stationary
distribution of the induced chain, it is the only one when `λ, q > 0`, and the purchase
probability under it is `λqX/(τ + q(X − τ + 1))`. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ)
    (τ : ℕ) (hτ1 : 1 ≤ τ) (hτX : τ + 1 ≤ X) (hB : CaseB P p X J τ) :
    MarkovChain.IsStationary (trans P p X J)
        (fun i => (if i.val < τ then 1 else P.q) / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1))) ∧
      (0 < P.lam → 0 < P.q → ∀ μ : Fin (X + 1) → ℝ, MarkovChain.IsStationary (trans P p X J) μ →
        μ = fun i => (if i.val < τ then 1 else P.q) / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1))) ∧
      (fun i : Fin (X + 1) =>
          (if i.val < τ then 1 else P.q) / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1))) ⬝ᵥ
          buyProb P p X J =
        P.lam * P.q * X / ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1)) := by sorry
end BuyXFree.Threshold
