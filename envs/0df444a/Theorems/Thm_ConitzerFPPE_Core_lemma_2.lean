-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_lemma_2
-- name    : ConitzerFPPE.Core.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:02:44.618897+00:00
-- url     : https://prove2.me/theorems/c00cc849-fcfb-44b4-a356-d56ce8a05eeb
-- title:
--   Lemma 2 (Guaranteed existence of FPPE)
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   Every Pareto-dominant BFPM $(\alpha,x)$ has no unnecessarily paced bidder and is an FPPE for that same allocation:
--   $$\bigl(\forall i,\ \neg(s_i(\alpha,x)<B_i\ \land\ \alpha_i<1)\bigr)\ \land\ (\alpha,x)\in\mathrm{FPPE}.$$
--   This retains the printed fixed-allocation assertion. Finding I1 records a numerical counterexample; no existential reallocation or extra hypothesis has been substituted.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Lemma 2, p. 10 (proof p. 11); https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsParetoDominant
import Definitions.Def_ConitzerFPPE_Core_IsFPPE
import Definitions.Def_ConitzerFPPE_Core_UnnecessarilyPaced

namespace ConitzerFPPE.Core

theorem lemma_2 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ)
    (hmax : IsParetoDominant P α x) :
    (∀ i, ¬ UnnecessarilyPaced P α x i) ∧ IsFPPE P α x := by sorry

end ConitzerFPPE.Core
