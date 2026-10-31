-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_lemma_4
-- name    : ConitzerFPPE.Core.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:01:29.643329+00:00
-- url     : https://prove2.me/theorems/132c1558-9077-42f5-b6d8-947bdd77bdb2
-- title:
--   Lemma 4 — Revenue monotonicity under multiplier dominance
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   For any two BFPM $(\alpha^{(1)},x^{(1)})$ and $(\alpha^{(2)},x^{(2)})$ with $\alpha^{(2)}_i\le\alpha^{(1)}_i$ for every bidder,
--   $$\operatorname{Rev}(\alpha^{(2)},x^{(2)})\le\operatorname{Rev}(\alpha^{(1)},x^{(1)}).$$
--   The allocations may differ. This is weak monotonicity of payments, with no strict-revenue conclusion.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Lemma 4, p. 12; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsBFPM
import Definitions.Def_ConitzerFPPE_Core_revenue

namespace ConitzerFPPE.Core

theorem lemma_4 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α₁ α₂ : N → ℝ) (x₁ x₂ : N → M → ℝ)
    (h₁ : IsBFPM P α₁ x₁) (h₂ : IsBFPM P α₂ x₂)
    (hdom : ∀ i, α₂ i ≤ α₁ i) :
    revenue P α₂ x₂ ≤ revenue P α₁ x₁ := by sorry

end ConitzerFPPE.Core
