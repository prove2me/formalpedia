-- Prove2me | Theorems.Thm_CutRankSched_state_count
-- name    : CutRankSched.state_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:37:22.579049+00:00
-- url     : https://prove2.me/theorems/8b1fa6a3-bf4b-4659-9846-9d4cf566f378
-- title:
--   Proof of Theorem 5.2 — at most $2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ}$ states per cut
-- statement:
--   Let $L \ge 1$ and $0 \le k \le n$, and let $q_k = \dim R_k$. The number of states Algorithm 1 holds at cut $k$ satisfies
--   $$
--   |\mathrm{DP}_k| \le 2^{q_k(q_k+1)/2}(L+1)^{q_k} L^{|F^\circ_k|} \le 2^{\kappa_\pi(\kappa_\pi+1)/2}(L+1)^{\kappa_\pi} L^{w^\circ}.
--   $$
--   The flags lie in $R_k$, of dimension $q_k \le \kappa_\pi$, and by Lemma 5.3 there are at most $2^{q_k(q_k+1)/2}(L+1)^{q_k}$ of them; the frontier has at most $L^{|F^\circ_k|} \le L^{w^\circ}$ labelings.
--
--   Differences from the source:
--   - generalization: at most 2^{O(κ_π²)}(L+1)^{κ_π} flags and L^{w°} labelings per cut → the explicit bound 2^{q_k(q_k+1)/2}(L+1)^{q_k}L^{|F°_k|} ≤ 2^{κ_π(κ_π+1)/2}(L+1)^{κ_π}L^{w°} on the number of states; reason: the explicit constant of Lemma 5.3 implies the O(κ_π²) form
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the count uses only the DP invariant; valid instances are a special case
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, pp.10–11

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_frontier
import Definitions.Def_CutRankSched_width
import Definitions.Def_CutRankSched_cutRank
import Definitions.Def_CutRankSched_rowSpace
import Definitions.Def_CutRankSched_dpSet

set_option autoImplicit false

namespace CutRankSched

/-- **Proof of Theorem 5.2, the state count per cut** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, pp.10–11). At
each cut `k`, the ambient row space `R_k` has dimension `q_k ≤ κ_π`; by Lemma 5.3 it admits at most
`2^{q_k(q_k+1)/2} (L+1)^{q_k}` descending weak flags, and the frontier has at most `L^{|F°_k|}`
labelings. So Algorithm 1 holds at most `2^{q_k(q_k+1)/2}(L+1)^{q_k}L^{|F°_k|} ≤
2^{κ_π(κ_π+1)/2}(L+1)^{κ_π}L^{w°}` states at cut `k`.

**Formalization Note** `q_k = finrank (rowSpace I k)`. The constants are Lemma 5.3's explicit
`2^{q(q+1)/2}` in place of `2^{O(κ_π²)}`. `State I L` is a finite type, so `ncard` counts. -/
theorem state_count (I : Instance) (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : k ≤ I.n) :
    (dpSet I L k).ncard ≤
        2 ^ (Module.finrank (ZMod 2) (rowSpace I k) * (Module.finrank (ZMod 2) (rowSpace I k) + 1) / 2) *
          (L + 1) ^ Module.finrank (ZMod 2) (rowSpace I k) * L ^ (frontier I k).card ∧
      2 ^ (Module.finrank (ZMod 2) (rowSpace I k) * (Module.finrank (ZMod 2) (rowSpace I k) + 1) / 2) *
          (L + 1) ^ Module.finrank (ZMod 2) (rowSpace I k) * L ^ (frontier I k).card ≤
        2 ^ (cutRank I * (cutRank I + 1) / 2) * (L + 1) ^ cutRank I * L ^ width I := by sorry

end CutRankSched
