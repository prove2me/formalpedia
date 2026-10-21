-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_proposition_5
-- name    : BleedFeed.ControlLimit.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:07.656215+00:00
-- url     : https://prove2.me/theorems/7560d257-844b-4e87-946f-d91c580592b8
-- title:
--   Proposition 5, p. 16 — $v(i,\mu,n)$ is nonincreasing in the bleed–feed count $n$
-- statement:
--   In the bleed–feed model (see the definition file), for every age $i\in\{0,\dots,I\}$, every growth rate $\mu\in\mathcal M$ and every $n<N$,
--   $$
--   v(i,\mu,n+1)\le v(i,\mu,n).
--   $$
--
--   Having used more of the $N$ permitted bleed–feeds never helps: the culture with more bleed–feeds left can imitate the other one. No condition on the model is needed. A consequence used next is $B(n+1)\le B(n)$.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), p. 16, Proposition 5

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit

/-- Proposition 5, p. 16: v(i, µ, n) is nonincreasing in n for fixed i ∈ {0, …, I} and µ ∈ ℳ. -/
theorem proposition_5 (P : Params) (hS : P.Standing) (i : ℕ) (hi : i ≤ P.I) (μ : ℝ)
    (hμ : μ ∈ P.rates) (n : ℕ) (hn : n < P.N) :
    v P i μ (n + 1) ≤ v P i μ n := by sorry

end BleedFeed.ControlLimit
