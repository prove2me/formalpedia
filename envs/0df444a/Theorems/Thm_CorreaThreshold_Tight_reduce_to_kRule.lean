-- Prove2me | Theorems.Thm_CorreaThreshold_Tight_reduce_to_kRule
-- name    : CorreaThreshold.Tight.reduce_to_kRule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:59.429354+00:00
-- url     : https://prove2.me/theorems/4f400b2a-e97d-42e2-bed0-38252f2ddea6
-- title:
--   §3.1 — every nonadaptive rule is dominated by a two-level rule
-- statement:
--   Fix $n\ge2$ and the Section 3.1 i.i.d. law. For every predetermined threshold vector $\tau\in[0,\infty]^{n^2}$, there is an integer $0\le k\le n^2$ such that the canonical two-level rule $\tau^{(k)}$ earns at least as much expected reward:
--
--   $$
--   V_n(\tau)\le V_n(\tau^{(k)}).
--   $$
--
--   This reduction ensures that the upper-bound analysis of two-level rules applies to every nonadaptive threshold rule, including rules with an infinite threshold at some coordinates.
--
--   **Formalization Note** The first $k$ coordinates are indices $0,\ldots,k-1$. Strict threshold crossing gives the two acceptance classes via thresholds $0$ and $1$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), https://doi.org/10.1287/moor.2020.1105, p. 1461, §3.1

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

namespace CorreaThreshold.Tight

open MeasureTheory

theorem reduce_to_kRule (n : ℕ) (hn : 2 ≤ n) :
    ∀ τ : Fin (n ^ 2) → ENNReal, ∃ k : ℕ, k ≤ n ^ 2 ∧ value n τ ≤ value n (kRule n k) := by sorry

end CorreaThreshold.Tight
