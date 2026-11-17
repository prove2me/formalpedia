-- Prove2me | Theorems.Thm_FixpReciprocal_Supplement_theorem_6_2
-- name    : FixpReciprocal.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:50:58.098201+00:00
-- url     : https://prove2.me/theorems/f00091fc-e647-4270-988b-a8347305855c
-- title:
--   Theorem 6.2 — multiplier vectors of budget-constrained GSP autobidding equilibria are FIXP-complete (one slot per item, unit CTRs)
-- statement:
--   A **GSP sponsored-shopping instance** has a bidder set $B$, an item set $\mathcal J$ partitioned into ownership sets $(\mathcal J_\ell)_{\ell\in B}$, a positive rational value $v_s$ of each item $s$ to its owner, and a positive rational budget $M_\ell$ of each bidder. There is one advertising slot per item and every click-through rate equals one. Bidder $\ell$ uses one multiplier $\alpha_\ell\in[0,1]$, bidding $b_s=\alpha_\ell v_s$ on each $s\in\mathcal J_\ell$. For a ranking $\sigma=(s_1,\dots,s_m)$ and $s_k\in\mathcal J_\ell$, the price is
--   $$c_k(\alpha,\sigma)=\max\big(\{b_{s_{k'}}:k<k'\le m,\ s_{k'}\notin\mathcal J_\ell\}\cup\{0\}\big),$$
--   and for a distribution $\pi$ over rankings, $P_\ell(\alpha,\pi)=\mathbb E_{\sigma\sim\pi}\big[\sum_{k:\,s_k\in\mathcal J_\ell}c_k(\alpha,\sigma)\big]$. The pair $(\alpha,\pi)$ is a **budget-constrained autobidding equilibrium** (Definition 6.1) if for every ranking $\sigma$ and bidder $\ell$:
--
--   1. $\pi(\sigma)>0\implies b_{s_1}\ge\dots\ge b_{s_m}$;
--   2. $P_\ell(\alpha,\pi)\le M_\ell$;
--   3. $P_\ell(\alpha,\pi)<M_\ell\implies\alpha_\ell=1$.
--
--   **Theorem.** Given such an instance, computing a multiplier vector $\alpha\in[0,1]^B$ of a budget-constrained autobidding equilibrium is
--
--   $$\text{FIXP-complete.}$$
--
--   Because this is a special case of the general model, hardness here also gives FIXP-completeness for general slot counts and click-through rates.
--
--   **Formalization Note** The problem is the published `budgetGSPProblemOn` restricted to `OneSlotUnitCTR`; a solution is a vector $\alpha$ for which some $\pi$ makes $(\alpha,\pi)$ an exact equilibrium (`IsApproxABEB 0`).
--
--   Differences from the source:
--   - reading: ownership sets (J_ℓ)_{ℓ∈B} that partition J → Auction.WellFormed: every bidder owns at least one item (and hence at least one bidder and one item, as 1 ≤ K = M); reason: the blocks of a partition are nonempty; this is the paper's own notion, not an added restriction
--   - encoding: the items of a bidder as an unordered set J_ℓ → each bidder's values listed in nonincreasing order (Auction.WellFormed); reason: the order of a bidder's items is presentation only: prices, payments and equilibria do not depend on item labels, and any instance is put in this form by sorting each list
--   - encoding: one slot per item, click-through rate one at every slot → OneSlotUnitCTR: K = M and every entry of the ctr list equals 1; K and the ctr list are part of the encoded instance; reason: the published auction carries K and the CTRs as data; with K = M and unit CTRs they are determined by the rest
--   - encoding: rankings σ of J and a probability distribution π over rankings → Auction.Alloc (bijections from ranks Fin M to items) and π : Alloc → ℝ, nonnegative with total 1; reason: the same objects
--   - encoding: price (17) and expected payment (18) → published price (maximum over bids of later-ranked items of other owners, together with 0) and expPayment with ctrAt = 1 at every rank; reason: with K = M and unit CTRs, Σ_k ctr_k · price_k is Σ_k price_k, which is (18)
--   - encoding: output: a multiplier vector α ∈ [0,1]^B of an equilibrium → solutions are α : Fin n → ℝ such that ∃ π with IsApproxABEB 0 α π ((19)–(21), α ∈ [0,1]^n); reason: the theorem asks for the multiplier vector only
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Theorem 6.2, p.22 (PDF p.24); §6.1 and Definition 6.1, pp.21–22 (PDF pp.23–24), (17)–(21)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_GSP
import Definitions.Def_FixpReciprocal_Supplement_Classes

namespace FixpReciprocal.Supplement

open ExactAutobid.Equilibria

/-- **Theorem 6.2 (Autobidding).** Given a GSP sponsored-shopping instance with one slot per item and
all click-through rates equal to one, computing a multiplier vector `α ∈ [0, 1]^B` of a
budget-constrained autobidding equilibrium (Definition 6.1) is FIXP-complete.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), Theorem 6.2, p.22; §6.1 and Definition 6.1, pp.21–22, (17)–(21).

**Formalization Note.** The problem is the published `budgetGSPProblemOn` restricted to
`OneSlotUnitCTR`: instances are auctions with positive rational item values, one positive rational
budget per bidder, `K = M` and unit click-through rates; a solution is a multiplier vector `α` for
which some distribution `π` over rankings makes `(α, π)` an exact equilibrium (`IsApproxABEB 0`:
(19)–(21) with the no-self-pricing price (17) and payment (18)). The published standing assumptions
require every bidder to own at least one item and list each bidder's values in nonincreasing order. -/
theorem theorem_6_2 :
    FIXPComplete (budgetGSPProblemOn OneSlotUnitCTR) := by sorry

end FixpReciprocal.Supplement
