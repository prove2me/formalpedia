-- Prove2me | Theorems.Thm_ConitzerFPPE_Core_lemma_1
-- name    : ConitzerFPPE.Core.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:02:05.449979+00:00
-- url     : https://prove2.me/theorems/1e3d9da6-2f70-4fd2-ba93-e1ec9aa7d561
-- title:
--   Lemma 1 — Existence of Pareto-dominant BFPM
-- statement:
--   Let $N,M$ be finite bidder and good sets, with real valuations $v_{ij}\ge0$ and budgets $B_i>0$. Multipliers and fractional allocations are real functions. Prices are highest paced bids, with zero adjoined; expenditure is $s_i=\sum_jx_{ij}p_j$ and revenue is $\operatorname{Rev}=\sum_i s_i$. BFPM and FPPE have the conditions in Definitions 1 and 2. Empty sets are included under these conventions.
--
--   There is a BFPM $(\alpha,x)$ whose multipliers dominate those of every BFPM:
--   $$\exists(\alpha,x)\in\mathrm{BFPM},\quad\forall(\beta,y)\in\mathrm{BFPM},\ \forall i,\ \beta_i\le\alpha_i.$$
--   Both the multiplier vector and its allocation are existence conclusions.
--
--   Differences from the source:
--   - encoding: bidder and good sets labelled by consecutive integers → arbitrary finite types with real multiplier and allocation functions; reason: relabeling by a finite-type equivalence preserves every market and condition
--   - generalization: the printed maximum presumes a nonempty bidder set → empty bidder sets are also allowed and their prices are zero; reason: adjoining zero to the finite maximum recovers the source maximum on every nonempty feasible market; empty markets satisfy the extended contracts
--   - encoding: unit prices and expenditure are written inside the feasibility conditions → separate price and spend functions, with revenue equal to total actual payments; reason: on feasible multipliers the zero-adjoined maximum and finite sums are exactly the source prices and payments
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Lemma 1, p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsParetoDominant

namespace ConitzerFPPE.Core

theorem lemma_1 {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) :
    ∃ (α : N → ℝ) (x : N → M → ℝ), IsParetoDominant P α x := by sorry

end ConitzerFPPE.Core
