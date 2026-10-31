-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_corollary_2
-- name    : ConitzerFPPE.Core.corollary_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:02:39.494536+00:00
-- url     : https://prove2.me/theorems/e1a34977-3ba6-4565-a958-2782123ffffe
-- title:
--   Corollary 2 (Revenue-maximizing)
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   Every FPPE $(\alpha,x)$ maximizes revenue over every BFPM of the same market:
--   $$\forall(\beta,y)\in\mathrm{BFPM},\quad\operatorname{Rev}(\beta,y)\le\operatorname{Rev}(\alpha,x).$$
--   Competitors need not be equilibria; equality is permitted.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Corollary 2, p. 12; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsFPPE
import Definitions.Def_ConitzerFPPE_Core_revenue

namespace ConitzerFPPE.Core

theorem corollary_2 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ)
    (h : IsFPPE P α x) :
    ∀ (β : N → ℝ) (y : N → M → ℝ),
      IsBFPM P β y → revenue P β y ≤ revenue P α x := by sorry

end ConitzerFPPE.Core
