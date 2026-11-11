-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_4_2
-- name    : AutobiddingGSP.Approximation.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:36.003549+00:00
-- url     : https://prove2.me/theorems/1f0965a9-c409-4109-9bee-3cc8592b3946
-- title:
--   Lemma 4.2 — legal insertion marginals give a bid-valid randomized allocation
-- statement:
--   Let $b$ be group bids (those induced by $\alpha$) and $\pi$ a probability distribution over insertion encodings with marginals $p_t$. If $p_{t,r}>0\Rightarrow r\in R_t(\alpha)$ for every step $2\le t\le T$ and position $r$, then every encoding $\sigma$ with $\pi(\sigma)>0$ produces a group order whose bids are nonincreasing.
--
--   Differences from the source:
--   - generalization: bids induced by a multiplier profile α → arbitrary real group bids b; reason: the induced bids are one choice of b
--   - encoding: π induces a bid-valid randomized allocation (of items) → every group order in the support of π has nonincreasing bids; reason: the items of a group share one bid and are expanded contiguously, so item validity is group validity
--   - encoding: steps 2 ≤ t ≤ T → 0-based steps 1 ≤ t ≤ T − 1; reason: Lean indexing
--   - generalization: the section assumes T ≥ 2 → any natural number T, including zero and one; reason: empty and singleton group orders are already nonincreasing; the sole insertion encoding carries probability one, and the original T ≥ 2 cases are unchanged
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 4.2, p. 14 (PDF 14)

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Insertion

namespace AutobiddingGSP.Approximation

/-- **Lemma 4.2** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 14 (PDF 14)). Fix group bids `b` (those induced by a multiplier profile
`α`). Let `π` be any probability distribution over deterministic group allocations (insertion
encodings) with insertion marginals `p_2, …, p_T`. If `p_{t,r} > 0 ⟹ r ∈ R_t(α)` for every
`2 ≤ t ≤ T` and `0 ≤ r ≤ t − 1`, then `π` induces a bid-valid randomized allocation: every group
order in its support lists the bids in nonincreasing order.

**Formalization Note** Steps are 0-based (Lean step `t ≥ 1` is the paper's step `t + 1 ≥ 2`). The
group bids are arbitrary reals. Expanding each group, whose items share one bid, into its items in
place keeps the order nonincreasing, so the group-level conclusion is the item-level one. -/
theorem lemma_4_2 {T : ℕ} (b : Fin T → ℝ) (π : InsSeq T → ℝ) (hπ0 : ∀ σ, 0 ≤ π σ)
    (hπ1 : ∑ σ, π σ = 1)
    (hleg : ∀ t : Fin T, 1 ≤ t.val → ∀ r : Fin (t.val + 1),
      0 < marginal π t r → IsLegal (prevBids b t) (b t) r.val) :
    ∀ σ, 0 < π σ → ((execute σ).map b).Pairwise (fun x y => y ≤ x) := by sorry

end AutobiddingGSP.Approximation
