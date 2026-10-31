-- Prove2me | Theorems.Thm_CongestionApproxPNE_case_two
-- name    : CongestionApproxPNE.case_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:48.428471+00:00
-- url     : https://prove2.me/theorems/9b3af791-93ac-433c-898f-73761673002c
-- title:
--   Proof of Theorem 1, Case 2 — a light player shares the heavy player's hub
-- statement:
--   Let $d\ge 2$, $n\in\mathbb N$, $k\in\{1,\dots,d\}$, $w\in(0,1]$ and $\beta\in[0,1]$, and consider the gadget $\mathcal G^d_{(n,k,w,\beta)}$ (heavy player of weight $1$, $n$ light players of weight $w$, hub costs $c_0(x)=x^k$, other costs $c_1(x)=\beta x^d$).
--   Let $h$ be one of the hubs $a_0$, $b_0$, and let $s$ be a profile in which the heavy player and some light player $i$ both use $h$. Then
--
--   $$
--   C_i(s)\ \ge\ c_0(1+w)+c_1(w)=(1+w)^k+\beta w^d,
--   $$
--
--   and after switching to her other strategy, player $i$'s cost satisfies
--
--   $$
--   C_i(s_i',s_{-i})\ \le\ c_0(nw)+c_1(1+w)=(nw)^k+\beta(1+w)^d .
--   $$
--
--   So in this case player $i$ improves by at least the factor $r_2=\frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}$, the second ratio of (3).
--
--   Differences from the source:
--   - encoding: Case stated for the heavy player on a₀, the b₀ case covered by "Due to symmetries" → a parameter h equal to a₀ or b₀, and the other strategy as any t ≠ s_i; reason: states both symmetric cases the proof uses; each player has exactly two strategies
--   - encoding: light weight w ∈ [0, 1] → w : ℝ≥0 with 0 < w ≤ 1; reason: §2 requires every weight to be positive, so a w = 0 member of the family is not a game; no game is lost
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, Case 2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_HarksKlimm_Consistency_load
import Definitions.Def_CongestionApproxPNE_playerCost
import Definitions.Def_CongestionApproxPNE_gadget

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **Case 2 of the proof of Theorem 1: a light player shares the heavy player's hub.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, Case 2, p.5: "The heavy player shares resource a0 with at least one
light player i ∈ {1, . . . , n}. Thus player i incurs a cost of at least c0(1 + w) + c1(w); while,
deviating to strategy {b0, ai}, she would incur a cost of at most c0(nw) + c1(1 + w)."

In the gadget `G^d_(n,k,w,β)` (`1 ≤ k ≤ d`, `0 < w ≤ 1`, `0 ≤ β ≤ 1`), let `h` be `a₀` or `b₀`,
used by the heavy player `0` and by the light player `i ≠ 0`. Then player `i`'s cost is at least
`(1+w)^k + βw^d`, and after switching to her other strategy it is at most `(nw)^k + β(1+w)^d`.

**Formalization Note** Both hubs (`a₀` and, "due to symmetries", `b₀`) are covered by the
parameter `h`. Player `i`'s other strategy is any `t ≠ s i` (she has exactly two). -/
theorem case_two (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) (hd : 2 ≤ d) (hk1 : 1 ≤ k)
    (hkd : k ≤ d) (hw1 : w ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (s : (gadget d n k w hw β).Profile) (h : Fin ((n + 1) + (n + 1)))
    (hh : h = Fin.castAdd (n + 1) 0 ∨ h = Fin.natAdd (n + 1) 0)
    (i : Fin (n + 1)) (hi : i ≠ 0) (hheavy : h ∈ (s 0).val) (hshare : h ∈ (s i).val) :
    (1 + (w : ℝ)) ^ k + β * (w : ℝ) ^ d ≤ playerCost (gadget d n k w hw β) s i ∧
      ∀ t : (gadget d n k w hw β).Strategy i, t ≠ s i →
        playerCost (gadget d n k w hw β) (Function.update s i t) i ≤
          ((n : ℝ) * (w : ℝ)) ^ k + β * (1 + (w : ℝ)) ^ d := by sorry

end CongestionApproxPNE
