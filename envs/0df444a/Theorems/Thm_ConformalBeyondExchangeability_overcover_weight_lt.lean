-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_overcover_weight_lt
-- name    : ConformalBeyondExchangeability.overcover_weight_lt
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:50:08.6884+00:00
-- url     : https://prove2.me/theorems/364a8ec4-4d0a-496e-91ff-663410ad48a8
-- title:
--   Eq. (37): deterministic bound behind the upper coverage bound
-- statement:
--   Let $w_1,\dots,w_n\in[0,1]$ with normalized weights $\tilde w_i$ (eq. (10)), and let $\alpha\in(0,1)$. For every $r\in\mathbb R^{n+1}$ with distinct entries $r_1,\dots,r_{n+1}$,
--   $$\sum_{k=1}^{n+1}\tilde w_k\cdot\mathbb 1\Big\{r_k\le\mathsf Q_{1-\alpha}\Big(\sum_{i=1}^{n+1}\tilde w_{\pi_k(i)}\delta_{r_i}\Big)\Big\}<1-\alpha+\tilde w_{n+1},$$
--   where $\pi_k$ swaps $k$ and $n+1$.
--
--   This is the deterministic inequality (37), from which Theorem 3 follows.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Appendix E.2, eq. (37), pp. 44-45

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem overcover_weight_lt {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) (hr : Function.Injective r) :
    ∑ k, normWeights w k *
        (if (r k : EReal) ≤
            wQuantile (fun i => normWeights w (swapIdx k i)) (fun i => (r i : EReal)) (1 - α)
          then 1 else 0) <
      1 - α + normWeights w (Fin.last n) := by sorry

end ConformalBeyondExchangeability
