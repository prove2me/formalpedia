-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_claim_3_2
-- name    : CloudMWU.Bicriteria.claim_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:19.976203+00:00
-- url     : https://prove2.me/theorems/65448f1a-19c6-4b32-af0c-f347c9dc22cb
-- title:
--   Claim 3.2 (first conclusion), p. 12 — in a block of m ≥ s̃ steps with a user busy throughout, at most 4εm steps have utilization ≤ 1 − ε
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$, let $\beta$ be any SLA vector, $L$ a nonnegative load sequence and $h$ a run of Algorithm 1. Let $c = \varepsilon\eta/(4N)$ and $\tilde s = \ln(N/\varepsilon)/(\varepsilon c)$. Let $r$ be a time and $m \ge \tilde s$ a natural number, and suppose some user $i_0$ has a non-empty queue at the start of every step $\tau \in [r, r+m]$. Let
--
--   $$B' = \Big\{\tau \in [r, r+m) : \sum_{j \in A_\tau} h_\tau(j) \le 1 - \varepsilon\Big\}$$
--
--   be the low-utilization steps of the block. Then
--
--   $$|B'| \le 4\varepsilon m.$$
--
--   This is the counting step of the proof of Theorem 3: on a block where some user is always busy, the resource is used at level more than $1 - \varepsilon$ by busy users except on a $4\varepsilon$ fraction of the steps.
--
--   **Formalization Note** Only the first conclusion of Claim 3.2 is stated. The paper's hypothesis $r > s^\star$ is used in its proof only through Claim 3.1, which provides the always-busy user; that user is the hypothesis here. Blocks have integer length $m \ge \tilde s$ (the paper's $\tilde s$ is real). Time is 0-based.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 12, Claim 3.2, first conclusion |B′| ≤ 4εs̃ (proof in Appendix B.2, pp. 28–29)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem claim_3_2 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (r m : ℕ) (hm : sTilde N ε η ≤ (m : ℝ))
    (i₀ : Fin N) (hbusy : ∀ τ ∈ Icc r (r + m), 0 < runQueue h L τ i₀) :
    (((Ico r (r + m)).filter (fun τ => ∑ j ∈ active h L τ, h τ j ≤ 1 - ε)).card : ℝ)
      ≤ 4 * ε * (m : ℝ) := by sorry

end CloudMWU.Bicriteria
