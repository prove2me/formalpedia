-- Prove2me | Theorems.Thm_CongestionApproxPNE_gadget_no_approx_pne
-- name    : CongestionApproxPNE.gadget_no_approx_pne
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:05.300084+00:00
-- url     : https://prove2.me/theorems/631cdcb3-5f15-48b5-9eff-af1fe229f46e
-- title:
--   Proof of Theorem 1 — the gadget has no $\alpha$-PNE for $\alpha$ below both ratios of (3)
-- statement:
--   Let $d\ge 2$, $n\in\mathbb N$, $k\in\{1,\dots,d\}$, $w\in(0,1]$ and $\beta\in[0,1]$, and consider the gadget $\mathcal G^d_{(n,k,w,\beta)}$ (heavy player of weight $1$, $n$ light players of weight $w$, hub costs $c_0(x)=x^k$, other costs $c_1(x)=\beta x^d$).
--   Then:
--
--   1. $\mathcal G^d_{(n,k,w,\beta)}$ is a polynomial congestion game of degree $d$;
--   2. for every $\alpha\ge 1$ with
--
--   $$
--   \alpha<\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta}\qquad\text{and}\qquad \alpha<\frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d},
--   $$
--
--   no strategy profile of $\mathcal G^d_{(n,k,w,\beta)}$ is an $\alpha$-PNE.
--
--   This is the step that turns the two cases of the proof into a nonexistence statement for a single gadget; maximizing over the family gives $\alpha(d)$.
--
--   Differences from the source:
--   - encoding: light weight w ∈ [0, 1] → w : ℝ≥0 with 0 < w ≤ 1; reason: §2 requires every weight to be positive, so a w = 0 member of the family is not a game; no game is lost
--   - encoding: polynomial cost functions c_e : ℝ>0 → ℝ≥0 → cost agrees with a polynomial at every load x ≥ 0 (x : ℝ≥0); reason: the load of a resource in a player's strategy is at least her positive weight, so the value at 0 never enters a cost; requiring it only narrows the class of games
--   - encoding: α-PNE for α ≥ 1; "both ratios are greater than α" → 1 ≤ α as a hypothesis, α-PNE predicate without the α ≥ 1 requirement; reason: the paper defines α-PNE only for α ≥ 1
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.5 (PDF p.6), "In order for the game to not have an α-PNE, it is enough to guarantee that both ratios are greater than α."

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_CongestionApproxPNE_IsApproxPNE
import Definitions.Def_CongestionApproxPNE_IsPolyGame
import Definitions.Def_CongestionApproxPNE_ratioOne
import Definitions.Def_CongestionApproxPNE_ratioTwo
import Definitions.Def_CongestionApproxPNE_gadget

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **The gadget is a polynomial game of degree `d` with no α-PNE below both ratios of (3).**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, p.5: "In order for the game to not have an α-PNE, it is enough to
guarantee that both ratios are greater than α."

For `d ≥ 2`, `n ∈ ℕ`, `k ∈ {1,…,d}`, `w ∈ (0,1]`, `β ∈ [0,1]`: the gadget `G^d_(n,k,w,β)` is a
polynomial congestion game of degree `d`, and for every `α ≥ 1` smaller than both
`(1 + nβ(1+w)^d)/((1+nw)^k + nβ)` and `((1+w)^k + βw^d)/((nw)^k + β(1+w)^d)`, no profile of it is
an α-PNE.

**Formalization Note** `w > 0` because weights are positive (§2). The game is
`HarksKlimm.Consistency.Game`; the ratios are `ratioOne`, `ratioTwo`. -/
theorem gadget_no_approx_pne (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) (hd : 2 ≤ d)
    (hk1 : 1 ≤ k) (hkd : k ≤ d) (hw1 : w ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsPolyGame d (gadget d n k w hw β) ∧
      ∀ α : ℝ, 1 ≤ α → α < ratioOne d n k (w : ℝ) β → α < ratioTwo d n k (w : ℝ) β →
        ∀ s : (gadget d n k w hw β).Profile, ¬ IsApproxPNE (gadget d n k w hw β) α s := by sorry

end CongestionApproxPNE
