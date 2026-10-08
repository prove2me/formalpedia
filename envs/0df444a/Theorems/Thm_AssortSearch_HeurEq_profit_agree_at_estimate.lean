-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_profit_agree_at_estimate
-- name    : AssortSearch.HeurEq.profit_agree_at_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:17.311557+00:00
-- url     : https://prove2.me/theorems/7bd32468-a5fe-4b66-8330-f05129a9054a
-- title:
--   Estimated and true profit agree at the estimating assortment: $\pi(x)=\pi(x\mid\hat v(x))$
-- statement:
--   In the independent assortment search model with $v_1,\dots,v_n>0$, $v_0>0$, $\lambda>0$, any margins $m_i$ and any cost function $c$, let $1\le x\le n$ and let $\hat v(x)$ be the preferences estimated from the sales of assortment $x$. Then the no-search model fed with $\hat v(x)$ reproduces the observed demands of assortment $x$, and so its profit prediction for $x$ is exact:
--   $$\pi(x)=\pi(x\mid\hat v(x)).$$
--
--   The proof of Theorem 8 uses this at the heuristic equilibrium, $\pi(x^*)=\pi(x^*\mid\hat v(x^*))$.
--
--   **Formalization Note** The paper states the identity at $x^*$; it holds, for the reason the paper gives, at every depth $1\le x\le n$, and it is stated so. No assumption on $m$ or $c$ is needed.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 23 (PDF 25), proof of Theorem 8, π(x*) = π(x*|v̂(x*))

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Proof of Theorem 8, p. 23 (`π(x*) = π(x* | v̂(x*))`): the no-search model fed with the
preferences estimated from an assortment `1 ≤ x ≤ n` reproduces the observed demands there, so the
estimated and the true profit of that assortment agree, `π(x) = π(x | v̂(x))`. -/
theorem profit_agree_at_estimate {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    trueProfit lam m c v v0 x =
      estProfit m c (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x := by sorry

end AssortSearch.HeurEq
