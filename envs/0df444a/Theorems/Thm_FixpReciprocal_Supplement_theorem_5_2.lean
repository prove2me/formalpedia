-- Prove2me | Theorems.Thm_FixpReciprocal_Supplement_theorem_5_2
-- name    : FixpReciprocal.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:50:00.568726+00:00
-- url     : https://prove2.me/theorems/e1fc2742-0907-4fb0-8eca-4143318deced
-- title:
--   Theorem 5.2 — exact second-price ROI pacing equilibria are FIXP-complete for every rational $\delta>0$
-- statement:
--   Fix a rational $\delta>0$. An instance consists of integers $n\ge2$ and $m\ge1$ and binary-encoded nonnegative rational values $v=(v_{\ell,s})_{\ell\in[n],s\in[m]}$ with $\max_{\ell\in[n]}v_{\ell,s}>0$ for every item $s$. Bidder $\ell$ bids $\alpha_\ell v_{\ell,s}$ on item $s$; $h_s(\alpha)$ is the highest bid and $p_s(\alpha)$ the second-highest bid on $s$, counting tied bids separately. A pair $(\alpha,z)\in[1,1+\delta]^n\times[0,1]^{n\times m}$ is a **second-price ROI pacing equilibrium** (Definition 5.1) if for all $\ell$ and $s$
--
--   1. $\sum_{\ell=1}^n z_{\ell,s}=1$;
--   2. $z_{\ell,s}>0\implies\alpha_\ell v_{\ell,s}=h_s(\alpha)$;
--   3. $\sum_{s=1}^m z_{\ell,s}p_s(\alpha)\le\sum_{s=1}^m z_{\ell,s}v_{\ell,s}$;
--   4. $\sum_{s=1}^m z_{\ell,s}p_s(\alpha)<\sum_{s=1}^m z_{\ell,s}v_{\ell,s}\implies\alpha_\ell=1+\delta$.
--
--   **Theorem.** For every fixed rational $\delta>0$, the search problem of finding an exact second-price ROI pacing equilibrium $(\alpha,z)$ of such an instance is
--
--   $$\text{FIXP-complete:}\quad\text{it lies in FIXP, and every problem in FIXP SL-reduces to it.}$$
--
--   This settles the exact complexity of ROI pacing equilibria in second-price auctions, which were known to lie in FIXP.
--
--   **Formalization Note** The problem is the published `roiPacingProblemOn (1 + δ)` restricted to the instance class `ShimizuPacing`; FIXP, SL-reductions and completeness are the mission's `FIXPComplete`.
--
--   Differences from the source:
--   - encoding: bidders ℓ ∈ [n], items s ∈ [m], values v_{ℓ,s} → PacingData with Fin nb, Fin ng (0-based) and one row of rational values per bidder; WellFormed gives nb rows of ng nonnegative entries; reason: Lean indexing; the same instances
--   - encoding: solution pair (α, z) ∈ [1, 1+δ]^n × [0,1]^{n×m} → one real vector y of dimension n + n·m, α = first n coordinates, z_{ℓ,s} = coordinate n + ℓ·m + s (pacingAlphaOf, pacingShareOf); reason: RealSearch solutions are single vectors; the published problem fixes this layout
--   - encoding: (7): Σ_ℓ z_{ℓ,s} = 1 for every item s → ValidAllocOn: Σ_ℓ z_{ℓ,s} = 1 whenever some bid on s is positive; reason: on these instances α_ℓ ≥ 1 and max_ℓ v_{ℓ,s} > 0, so every item has a positive bid and the two conditions coincide
--   - encoding: (8): z_{ℓ,s} > 0 ⟹ α_ℓ v_{ℓ,s} = h_s(α) → z_{ℓ,s} > 0 ⟹ every bid on s is at most α_ℓ v_{ℓ,s}; reason: h_s is the highest bid, so both say the bid of ℓ is the maximum
--   - encoding: price p_s(α): the second-highest bid, counting tied bids separately → secondPrice: entry 1 (0-based) of the bids sorted in nonincreasing order with repetitions; reason: the same number; it exists since n ≥ 2
--   - encoding: for every fixed rational δ > 0 → δ : ℚ with 0 < δ quantified outside FIXPComplete; the cap of the published problem is A = 1 + δ; reason: δ is a parameter of the problem, not instance data, so machines may depend on it, as for τ in the mission's goal
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Theorem 5.2, p.17 (PDF p.19); §5.1 and Definition 5.1, pp.16–17 (PDF pp.18–19), (7)–(10)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing
import Definitions.Def_FixpReciprocal_Supplement_Classes

namespace FixpReciprocal.Supplement

open ExactAutobid.Equilibria

/-- **Theorem 5.2 (ROI-constrained pacing).** For every fixed rational `δ > 0`, the following search
problem is FIXP-complete: given integers `n ≥ 2`, `m ≥ 1` and binary-encoded nonnegative rational
values `v` with `max_ℓ v_{ℓ,s} > 0` for every item `s`, find an exact second-price ROI pacing
equilibrium `(α, z) ∈ [1, 1 + δ]^n × [0, 1]^{n×m}` (Definition 5.1).

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), Theorem 5.2, p.17; Definition 5.1, pp.16–17.

**Formalization Note.** The problem is the published `roiPacingProblemOn` with cap `A = 1 + δ`,
restricted to `ShimizuPacing`; a solution is the vector `(α, z)` of dimension `n + n m`. On these
instances every item has a positive bid, so the published "shares sum to one if some bid is positive"
is (7); "a positive share only for a highest bidder" is (8); `secondPrice` (second entry of the bids
sorted with repetitions) is `p_s`; `ROICondOn` with cap `1 + δ` is (9)–(10). `δ` is a parameter of the
problem, so machines may depend on it. -/
theorem theorem_5_2 (δ : ℚ) (hδ : 0 < δ) :
    FIXPComplete (roiPacingProblemOn (1 + δ) ShimizuPacing) := by sorry

end FixpReciprocal.Supplement
