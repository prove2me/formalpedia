-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_6_2
-- name    : ExactAutobid.Equilibria.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:11.253254+00:00
-- url     : https://prove2.me/theorems/f9d83619-f0eb-45af-af3c-109bca53721b
-- title:
--   Lemma 6.2 — identical-supplier bounds in unit-CTR full-display no-self-pricing GSP
-- statement:
--   In a unit-CTR, full-display no-self-pricing GSP auction, let $S$ be a group of $n = |S| \ge 2$ suppliers with identical catalogs of positive values that include a pair $w, 2w$ in ratio two. Let $\pi$ be a distribution over orders valid at $\alpha$, and suppose $\alpha_b \ge 1$ and $P_b \le V_b$ for every $b \in S$. Then:
--   - if two suppliers of $S$ have unequal multipliers, the minimum multiplier in $S$ is one;
--   - every supplier multiplier is at most two;
--   - if all suppliers share a common multiplier $\alpha_{\mathrm{grp}}$, then
--   $$\alpha_{\mathrm{grp}} \le \frac{n}{n-1}.$$
--
--   These bounds hold before any ordering or gate equation is used, and anchor the supplier blocks of the ROI-GSP reduction.
--
--   Differences from the source:
--   - encoding: unit-CTR, full-display → K = number of goods, ctr of length K with every entry 1; reason: published Auction fields
--   - encoding: identical catalogs whose positive values include a pair in ratio two → catalog value lists equal up to permutation (List.Perm), all positive, and some member's catalog containing w and 2w; reason: catalogs are multisets of values; with identical catalogs one member suffices
--   - generalization: multipliers of the bidders outside the group (in the model's domain) → arbitrary reals; reason: the proof compares only supplier bids; any model domain is a special case
--   - generalization: a GSP auction of the model (positive values for every bidder, the standing assumptions of §2.1) → any Auction record with K = number of goods and unit CTRs: no Auction.WellFormed, catalogs of bidders outside the group arbitrary rationals; reason: outside goods only enter supplier prices as a maximum with the supplier copies' bids, which the proof (C.2) uses as lower bounds; every model auction is an instance
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 33 (PDF 35), Lemma 6.2

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Model

open AutobiddingGSP.Approximation

namespace ExactAutobid.Equilibria

/-- **Lemma 6.2 (Identical-Supplier Bounds).** In a unit-CTR, full-display no-self-pricing GSP
auction, let `S` be a group of `n ≥ 2` suppliers with identical catalogs of positive values that
include a pair in ratio two, with multipliers at least one and satisfying ROI feasibility under a
distribution `π` over valid orders. Unequal multipliers force the minimum multiplier of the group
to be one; every supplier multiplier is at most two; and a common multiplier `α_grp` of all `n`
suppliers satisfies `α_grp ≤ n/(n − 1)`. -/
theorem lemma_6_2 (Au : Auction) (hK : Au.K = Au.numItems) (hlen : Au.ctr.length = Au.K)
    (hctr : ∀ q ∈ Au.ctr, q = 1) (S : Finset (Fin Au.n)) (hS : 2 ≤ S.card)
    (hident : ∀ i ∈ S, ∀ i' ∈ S, (Au.vals.get i).Perm (Au.vals.get i'))
    (hpos : ∀ i ∈ S, ∀ q ∈ Au.vals.get i, 0 < q)
    (hpair : ∃ i ∈ S, ∃ w ∈ Au.vals.get i, 2 * w ∈ Au.vals.get i)
    (α : Fin Au.n → ℝ) (π : Au.Alloc → ℝ) (hπ : Au.IsDist π)
    (hvalid : ∀ a, 0 < π a → Au.IsValidAlloc α a) (hge : ∀ i ∈ S, 1 ≤ α i)
    (hroi : ∀ i ∈ S, Au.expPayment α π i ≤ Au.expValue π i) :
    ((∃ i ∈ S, ∃ i' ∈ S, α i ≠ α i') → ∃ i ∈ S, α i = 1) ∧
    (∀ i ∈ S, α i ≤ 2) ∧
    ∀ a : ℝ, (∀ i ∈ S, α i = a) → a ≤ (S.card : ℝ) / ((S.card : ℝ) - 1) := by sorry

end ExactAutobid.Equilibria
