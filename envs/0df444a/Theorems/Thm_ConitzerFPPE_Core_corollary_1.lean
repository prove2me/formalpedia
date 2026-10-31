-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_corollary_1
-- name    : ConitzerFPPE.Core.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:02:23.281815+00:00
-- url     : https://prove2.me/theorems/468ac7b1-fa1f-41fe-b982-72a6b62e618a
-- title:
--   Corollary 1 (Essential Uniqueness)
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   For every FPPE $(\alpha,x)$, its multiplier vector is greatest among BFPM multipliers. Every Pareto-dominant BFPM $(\beta,y)$ and every FPPE $(\gamma,z)$ satisfy
--   $$\beta=\alpha=\gamma.$$
--   Thus the multipliers agree with those of the maximal BFPM and are unique across equilibria. Allocation equality is not asserted.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Corollary 1, p. 11; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsFPPE
import Definitions.Def_ConitzerFPPE_Core_IsParetoDominant

namespace ConitzerFPPE.Core

theorem corollary_1 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ)
    (h : IsFPPE P α x) :
    IsParetoDominant P α x ∧
    (∀ (β : N → ℝ) (y : N → M → ℝ), IsParetoDominant P β y → β = α) ∧
    (∀ (β : N → ℝ) (y : N → M → ℝ), IsFPPE P β y → β = α) := by sorry

end ConitzerFPPE.Core
