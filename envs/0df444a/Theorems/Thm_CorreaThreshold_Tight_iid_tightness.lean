-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_iid_tightness
-- name    : CorreaThreshold.Tight.iid_tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:24.105645+00:00
-- url     : https://prove2.me/theorems/a199008f-b4b7-4003-aeef-e3a4058d2671
-- title:
--   §3.1 — i.i.d. tightness of the nonadaptive 1 − 1/e guarantee
-- statement:
--   For each $n\ge2$, take $n^2$ i.i.d. rewards from the three point law with values $0$, $1$, and $n/(e-2)$ and probabilities given in Section 3.1. Let $P_n$ be the prophet's expected maximum and $V_n(\tau)$ the expected reward of a fixed nonadaptive threshold vector under uniformly random arrival order. For every $\varepsilon>0$, there is $N$ such that every $n\ge N$ and every $\tau\in[0,\infty]^{n^2}$ satisfy
--
--   $$
--   V_n(\tau)<(1+\varepsilon)(1-e^{-1})P_n.
--   $$
--
--   Hence the paper's $1-1/e$ guarantee cannot be improved within this rule class, even for identically distributed rewards.
--
--   **Formalization Note** The proof in Appendix B supports the stronger eventual form of Section 3.1's existence claim. The universal quantifier ranges over all extended nonnegative thresholds, not merely the canonical two-level rules. The expected reward is the paper's random-order ratio with strict threshold crossing and $0/0=0$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, pp. 1460–1461, §3.1, proved p. 1474, Appendix B

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem iid_tightness :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ τ : Fin (n ^ 2) → ENNReal,
        value n τ <
          ENNReal.ofReal ((1 + ε) * (1 - Real.exp (-1))) * prophet n := by sorry

end CorreaThreshold.Tight
