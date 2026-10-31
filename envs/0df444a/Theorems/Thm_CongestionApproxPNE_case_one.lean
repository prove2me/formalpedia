-- Prove2me | Theorems.Thm_CongestionApproxPNE_case_one
-- name    : CongestionApproxPNE.case_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:28.169648+00:00
-- url     : https://prove2.me/theorems/392ddb1b-07b5-4db0-9927-b239f903e093
-- title:
--   Proof of Theorem 1, Case 1 — the heavy player alone on her hub
-- statement:
--   Let $d\ge 2$, $n\in\mathbb N$, $k\in\{1,\dots,d\}$, $w\in(0,1]$ and $\beta\in[0,1]$, and consider the gadget $\mathcal G^d_{(n,k,w,\beta)}$ (heavy player of weight $1$, $n$ light players of weight $w$, hub costs $c_0(x)=x^k$, other costs $c_1(x)=\beta x^d$).
--   Let $h$ be one of the hubs $a_0$, $b_0$, and let $s$ be a profile in which the heavy player uses $h$ and no light player does. Then every light player sits on the opposite hub, and
--
--   $$
--   C_0(s)=c_0(1)+n\,c_1(1+w)=1+n\beta(1+w)^d,
--   $$
--
--   while after switching to her other strategy the heavy player's cost is
--
--   $$
--   C_0(s_0',s_{-0})=c_0(1+nw)+n\,c_1(1)=(1+nw)^k+n\beta .
--   $$
--
--   So in this case the heavy player improves by the factor $r_1=\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta}$, the first ratio of (3).
--
--   Differences from the source:
--   - encoding: Case stated for the heavy player on a₀, the b₀ case covered by "Due to symmetries" → a parameter h equal to a₀ or b₀, and the other strategy as any t ≠ s_i; reason: states both symmetric cases the proof uses; each player has exactly two strategies
--   - encoding: light weight w ∈ [0, 1] → w : ℝ≥0 with 0 < w ≤ 1; reason: §2 requires every weight to be positive, so a w = 0 member of the family is not a game; no game is lost
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, Case 1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_HarksKlimm_Consistency_load
import Definitions.Def_CongestionApproxPNE_playerCost
import Definitions.Def_CongestionApproxPNE_gadget

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **Case 1 of the proof of Theorem 1: the heavy player alone on her hub resource.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, Case 1, p.5: "The heavy player is alone on resource a0. This means
that every light player i ∈ {1, . . . , n} must have chosen strategy {b0, ai}. Thus the heavy player
incurs a cost of c0(1) + nc1(1+w); while, deviating to strategy {b0, . . . , bn}, she would incur a
cost of c0(1+nw)+nc1(1)."

In the gadget `G^d_(n,k,w,β)` (`1 ≤ k ≤ d`, `0 < w ≤ 1`, `0 ≤ β ≤ 1`), let `h` be `a₀` or `b₀`,
used by the heavy player `0` and by no light player. Then the heavy player's cost is
`1 + nβ(1+w)^d`, and after switching to her other strategy it is `(1+nw)^k + nβ`.

**Formalization Note** The paper treats `h = a₀` and covers `h = b₀` "due to symmetries"; both
are stated here (`h` is either hub). The heavy player's other strategy is any `t ≠ s 0` (she has
exactly two). Player `0` is the heavy player; see `gadget` for the resource numbering. -/
theorem case_one (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) (hd : 2 ≤ d) (hk1 : 1 ≤ k)
    (hkd : k ≤ d) (hw1 : w ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (s : (gadget d n k w hw β).Profile) (h : Fin ((n + 1) + (n + 1)))
    (hh : h = Fin.castAdd (n + 1) 0 ∨ h = Fin.natAdd (n + 1) 0)
    (hheavy : h ∈ (s 0).val) (halone : ∀ i : Fin (n + 1), i ≠ 0 → h ∉ (s i).val) :
    playerCost (gadget d n k w hw β) s 0 = 1 + (n : ℝ) * β * (1 + (w : ℝ)) ^ d ∧
      ∀ t : (gadget d n k w hw β).Strategy 0, t ≠ s 0 →
        playerCost (gadget d n k w hw β) (Function.update s 0 t) 0 =
          (1 + (n : ℝ) * (w : ℝ)) ^ k + (n : ℝ) * β := by sorry

end CongestionApproxPNE
