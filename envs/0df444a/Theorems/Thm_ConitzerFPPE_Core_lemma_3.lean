-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_lemma_3
-- name    : ConitzerFPPE.Core.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:01:27.569988+00:00
-- url     : https://prove2.me/theorems/fec17da5-cf3c-43e7-acf4-5bba669151a5
-- title:
--   Lemma 3 — Strict multiplier dominance forces unnecessary pacing
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   Suppose $(\alpha^{(1)},x^{(1)})$ and $(\alpha^{(2)},x^{(2)})$ are BFPM, with $\alpha^{(2)}_i\le\alpha^{(1)}_i$ for every bidder and a strict inequality for at least one bidder. Then
--   $$\exists i,\quad s_i(\alpha^{(2)},x^{(2)})<B_i\ \land\ \alpha^{(2)}_i<1.$$
--   The unnecessarily paced bidder need not be the particular bidder witnessing strict dominance.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Lemma 3, p. 11; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsBFPM
import Definitions.Def_ConitzerFPPE_Core_UnnecessarilyPaced

namespace ConitzerFPPE.Core

theorem lemma_3 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α₁ α₂ : N → ℝ) (x₁ x₂ : N → M → ℝ)
    (h₁ : IsBFPM P α₁ x₁) (h₂ : IsBFPM P α₂ x₂)
    (hdom : ∀ i, α₂ i ≤ α₁ i) (hstrict : ∃ i, α₂ i < α₁ i) :
    ∃ i, UnnecessarilyPaced P α₂ x₂ i := by sorry

end ConitzerFPPE.Core
