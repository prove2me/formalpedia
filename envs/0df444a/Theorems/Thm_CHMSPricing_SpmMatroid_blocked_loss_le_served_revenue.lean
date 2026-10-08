-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_blocked_loss_le_served_revenue
-- name    : CHMSPricing.SpmMatroid.blocked_loss_le_served_revenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:41:12.359767+00:00
-- url     : https://prove2.me/theorems/4bafb056-e26d-484a-b96f-dff815db9b91
-- title:
--   §4.1, proof of Theorem 5, p. 7 — the revenue lost on blocked agents is at most the revenue of the served set
-- statement:
--   Let $\mathcal J$ be a matroid on $[n]$, and let $q_1, \dots, q_n \ge 0$ satisfy $\sum_{i \in T} q_i \le \operatorname{rank}(T)$ for every $T \subseteq [n]$. Run the sequential posted-price mechanism with nonnegative prices $\mathbf p$, approaching the agents in decreasing order of price, on any value profile $\mathbf v$; let $S$ be the set of agents served and $B$ the set of blocked agents (those not offered service at their turn). Then
--
--   $$\sum_{i \in B} p_i\, q_i \le \sum_{i \in S} p_i.$$
--
--   This is the deterministic core of the proof of Theorem 5: conditioned on the served set, the revenue lost because blocked agents could not be offered service is paid for by the served agents.
--
--   **Formalization Note** The page groups the blocked agents into the sets $B_j = \operatorname{span}(S_j) \setminus \operatorname{span}(S_{j-1})$; the statement is about their union and needs no span. The last expression of the page's display, $\sum_{1 \le j < \ell} p^j$, is a typo for $\sum_{1 \le j \le \ell} p^j$, "the revenue obtained by serving $S$", as the next sentence says and the telescoping gives; the statement uses the corrected sum.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 7, §4.1, proof of Theorem 5, first display and the sentence after it

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §4.1, proof of Theorem 5 (p. 7, first display): in one run of the SPM under a matroid
constraint, with nonnegative prices offered in decreasing order and weights `qᵢ ≥ 0` satisfying
`∑_{i ∈ T} qᵢ ≤ rank(T)` for every `T`, the revenue lost on the blocked agents,
`∑_{i blocked} pᵢ qᵢ`, is at most the revenue `∑_{i ∈ S} pᵢ` of the served set `S`. -/
theorem blocked_loss_le_served_revenue {n : ℕ} (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, q i ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) (v : Fin n → ℝ) :
    ∑ i ∈ spmBlocked J σ p v, p i * q i ≤
      ∑ i ∈ spmServed J σ p v, p i := by sorry

end CHMSPricing.SpmMatroid
