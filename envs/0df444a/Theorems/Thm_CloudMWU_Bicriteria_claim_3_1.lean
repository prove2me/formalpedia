-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_claim_3_1
-- name    : CloudMWU.Bicriteria.claim_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:11.715238+00:00
-- url     : https://prove2.me/theorems/57d4b484-0505-49c6-a187-f150202b7deb
-- title:
--   Claim 3.1, p. 12 — if condition (7) fails at r, some user's queue is non-empty throughout the block [r, r + m] (0-based form)
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$, let $\beta$ be any SLA vector, $L$ a nonnegative load sequence and $h$ a run of Algorithm 1. Let $r, m$ be natural numbers such that
--
--   $$\sum_{\tau < r + m} \sum_i w_\tau(i) \;<\; \sum_{\tau < r} \sum_i L_\tau(i),$$
--
--   that is, the work done in the first $r + m$ steps falls short of the load that arrived in the first $r$ steps (condition (7) of the paper fails at $s = r$). Then there is a user $i$ whose queue is non-empty at the start of every step $r' \in [r, r + m]$.
--
--   In the proof of Theorem 3, $r$ is any time after $s^\star$, the last time at which condition (7) holds, and $m$ is the block length $\tilde s$; the claim produces a user that stays busy throughout the block.
--
--   **Formalization Note** Time is 0-based: the queue at Lean time $r'$ is the queue before the load of that step arrives, so an empty queue at $r'$ means that exactly the load of the first $r'$ steps has been completed. The printed proof identifies the work up to $r'$ with the load up to $r'$ *including* step $r'$; the 0-based statement is the corrected form, equal to the printed claim for blocks starting one step later. The paper's "$r > s^\star$" is replaced by the property of such $r$ that the proof uses (the failure of (7) at $r$). Queues start empty.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 12, Claim 3.1 and condition (7)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem claim_3_1 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (r m : ℕ)
    (hfail : totalWork h L (r + m) < totalLoad L r) :
    ∃ i : Fin N, ∀ r' ∈ Icc r (r + m), 0 < runQueue h L r' i := by sorry

end CloudMWU.Bicriteria
