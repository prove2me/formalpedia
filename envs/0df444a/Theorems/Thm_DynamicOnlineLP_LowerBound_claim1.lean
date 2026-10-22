-- Prove2me | Theorems.Thm_DynamicOnlineLP_LowerBound_claim1
-- name    : DynamicOnlineLP.LowerBound.claim1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:12:04.139977+00:00
-- url     : https://prove2.me/theorems/3ccad566-8739-40eb-8417-6c91bf02c66b
-- title:
--   Claim 1 — a (1 − ε)-competitive solution of the constructed instance accepts close to B/z vectors w_i: Σ_i |r_i − B/z| ⩽ 7εB
-- statement:
--   Consider the constructed instance of the lower-bound construction with $z\ge 1$ pairs, $m=2^z$ items, capacity $B=zk$ for every item (so $B/z=k$), and for each pair $i$: $k$ inputs $(4,v_i)$, $q_i$ inputs $(3,w_i)$, $s$ inputs $(2,w_i)$ and $2k-q_i$ inputs $(1,w_i)$, where $q_i\le 2k$ and $s\ge 0$ are arbitrary. Let $\varepsilon\in\mathbb R$ and let $x$ be a **$(1-\varepsilon)$-competitive solution**: a feasible solution of the offline linear program ($\sum_c a_{jc}x_c\le B$ for every item $j$, $0\le x_c\le 1$) whose objective satisfies $\sum_c\pi_c x_c\ge(1-\varepsilon)\,\mathrm{OPT}$. Let $r_i=\sum x_c$ over the inputs of pair $i$ with demand vector $w_i$. Then
--
--   $$\sum_{i}\Bigl|\,r_i-\frac{B}{z}\Bigr|\le 7\varepsilon B .$$
--
--   In words, a near-optimal solution must accept almost exactly $B/z$ of the $w_i$-inputs of every pair, whatever the realized numbers $q_i$ of profit-3 inputs are. This is the combinatorial half of the lower bound (Theorem 2): an online algorithm must commit to accepting or rejecting the profit-2 inputs of pair $i$ before it can tell whether $q_i$ exceeds $B/z$, and Claim 1 says each wrong commitment costs profit.
--
--   **Formalization Note** $r_i$ counts accepted $w_i$-inputs fractionally ($x_c\in[0,1]$), as in the linear program (1). The claim is stated for every $\varepsilon\in\mathbb R$ (for $\varepsilon<0$ there is no such solution unless $\mathrm{OPT}\le 0$) and for any number $s$ of profit-2 inputs; the paper's instance has $s=\sqrt{B/4z}$ and its proof never uses the value of $s$. $B/z=k$ is a natural number, as the page's "$B/z$ inputs" requires.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 886, Claim 1

import Mathlib
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP
import Definitions.Def_DynamicOnlineLP_LowerBound_HardInstance

namespace DynamicOnlineLP.LowerBound

/-- Agrawal–Wang–Ye 2014, Claim 1 (p. 886). In the constructed instance (`m = 2^z` items, `B = z k`
units of each, `B/z = k`, any number `s` of profit-2 inputs per pair, any `q_i ≤ 2k`), let `x` be a
feasible solution of the offline problem (1) that is `1 - ε` competitive, i.e. its objective is at
least `(1 - ε) OPT`, and let `r_i` be the amount of `w_i`-inputs it accepts. Then
`∑_i |r_i - B/z| ≤ 7 ε B`. -/
theorem claim1 (z k s : ℕ) (hz : 1 ≤ z) (q : Fin z → ℕ) (hq : ∀ i, q i ≤ 2 * k) (ε : ℝ)
    (x : HardCol z k s q → ℝ) (hx : IsFeasible (hardDemand z k s q) (hardCapacity z k) x)
    (hcomp : (1 - ε) * OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k) ≤
      objective (hardProfit z k s q) x) :
    ∑ i : Fin z, |acceptedW x i - (k : ℝ)| ≤ 7 * ε * ((z : ℝ) * (k : ℝ)) := by sorry

end DynamicOnlineLP.LowerBound
