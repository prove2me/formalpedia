-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_remark_1
-- name    : BleedFeed.ControlLimit.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:37.88973+00:00
-- url     : https://prove2.me/theorems/9e64fe60-01bc-4a6b-a1e2-b357f0bdfe0e
-- title:
--   Remark 1, p. 14 — before the critical age, continuing is optimal and $v(i,\mu,n)$ is nonincreasing in $i$
-- statement:
--   In the bleed–feed model (see the definition file), fix a growth rate $\mu\in\mathcal M$, a bleed–feed count $n\le N$ and an age $i<\tilde\imath_\mu$ below the critical age. Then
--
--   1. if $i+1<I$, continuing is optimal in state $(i,\mu,n)$, i.e. $B(n)\le C(i,\mu,n)$;
--   2. if $i<I$, the value function does not increase from $i$ to $i+1$:
--   $$
--   v(i+1,\mu,n)\le v(i,\mu,n).
--   $$
--
--   Before the critical age there is no risk of entering the stationary phase, so waiting costs nothing; the remark is the "easy half" of the age monotonicity, the other half needing Condition (4).
--
--   **Formalization Note** The page claims continuation is optimal for every $i<\tilde\imath_\mu$; at $i=I-1<\tilde\imath_\mu$ continuing yields only $r_{I-1,\mu}$, which can be below $B(n)$, so item 1 carries the added hypothesis $i+1<I$. Item 2 holds for all $i<\min(\tilde\imath_\mu,I)$ as printed.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 14, Remark 1

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Remark 1, p. 14: for µ ∈ ℳ, n ≤ N and i < ĩ_µ, continuing is optimal (when i + 1 < I) and
v(i + 1, µ, n) ≤ v(i, µ, n) (when i < I). -/
theorem remark_1 (P : Params) (hS : P.Standing) (μ : ℝ) (hμ : μ ∈ P.rates) (n : ℕ) (hn : n ≤ P.N)
    (i : ℕ) (hi : i < critAge P μ) :
    (i + 1 < P.I → ContOpt P i μ n) ∧ (i < P.I → v P (i + 1) μ n ≤ v P i μ n) := by sorry

end BleedFeed.ControlLimit
