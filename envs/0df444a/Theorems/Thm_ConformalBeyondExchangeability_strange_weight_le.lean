-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_strange_weight_le
-- name    : ConformalBeyondExchangeability.strange_weight_le
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:47:56.826697+00:00
-- url     : https://prove2.me/theorems/d9b6cce9-168d-4994-be90-7d45135b9d71
-- title:
--   Eq. (25): the weighted fraction of strange points is at most $\alpha$
-- statement:
--   Let $w_1,\dots,w_n\in[0,1]$ with normalized weights $\tilde w_1,\dots,\tilde w_{n+1}$ (eq. (10)), and let $\alpha\in(0,1)$. For $r\in\mathbb R^{n+1}$ let
--   $$\mathcal S(r)=\Big\{i\in[n+1]:r_i>\mathsf Q_{1-\alpha}\Big(\sum_{j=1}^{n+1}\tilde w_j\delta_{r_j}\Big)\Big\}$$
--   be the set of strange points (eq. (24)). Then for all $r\in\mathbb R^{n+1}$,
--   $$\sum_{i\in\mathcal S(r)}\tilde w_i\le\alpha.$$
--
--   This deterministic inequality is the last step of the proof of Theorem 2.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 6.2, eqs. (24)-(25), p. 31

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem strange_weight_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → ℝ) :
    ∑ i ∈ strangeSet (normWeights w) α r, normWeights w i ≤ α := by sorry

end ConformalBeyondExchangeability
