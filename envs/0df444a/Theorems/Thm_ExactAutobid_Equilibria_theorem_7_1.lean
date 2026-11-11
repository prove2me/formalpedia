-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_7_1
-- name    : ExactAutobid.Equilibria.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:05.425902+00:00
-- url     : https://prove2.me/theorems/b7448d1b-0b89-4c97-90eb-152749583162
-- title:
--   Theorem 7.1 — second-price throttling is FIXP-complete (and FIXPa-complete) on sparse fixed-data instances
-- statement:
--   Finding an exact second-price throttling equilibrium $\theta$ is **FIXP-complete under SL reductions**, and approximating the participation vector in distance to an exact equilibrium is **FIXPa-complete**. There are finite sets of positive rational bids and budgets such that both hold already on the markets with at most four positive bids per bidder, at most three per good, a common tie priority across auctions, and all positive bids and budgets in those sets:
--   $$\mathrm{FIXPComplete}(\Pi_T) \wedge \mathrm{FIXPaComplete}(\Pi_T^{\approx}) \wedge \exists\, \mathcal{B}, \mathcal{W}\; \big(\mathrm{FIXPComplete}(\Pi_T|_{\mathcal{B},\mathcal{W}}) \wedge \mathrm{FIXPaComplete}(\Pi_T|_{\mathcal{B},\mathcal{W}}^{\approx})\big).$$
--
--   This is part (iv) of Theorem 1.1, the exact counterpart of the approximate hardness of CKK22.
--
--   Differences from the source:
--   - encoding: a common tie priority across auctions → the priority is part of the instance, a permutation of the bidders (list prio), used for every good; reason: Definition 2.4
--   - reading: hardness holds with ... positive bids and budgets in fixed finite rational sets → ∃ finite sets Bids, Budgets of positive rationals before the instance, with FIXPComplete and FIXPaComplete on ThrottleData.Sparse Bids Budgets; reason: constants quantified before the instance
--   - encoding: approximating the control vector within a supplied rational ε > 0 in ℓ∞ of some exact equilibrium → StrongApprox P k: instances (I, ε) with rational ε > 0, answers rational lists of length k(I) within ε of the first k(I) coordinates of some y ∈ Sol(I); reason: the controls are the first coordinates of every solution vector of this mission
--   - reading: FIXPa (reduction notion not spelled out in the paper; [EY10]) → InFIXPa D := polynomial-time search reduction (instance map f, answer map g, every answer of f(I) mapped to an answer of I) from D to StrongApprox basicFIXP (whole fixed point); FIXPa-hard/complete accordingly; reason: EY10's definition of FIXPa through polynomial-time search reductions; the paper uses it without restating it
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 50 (PDF 52), Theorem 7.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_FIXPa
import Definitions.Def_ExactAutobid_Equilibria_Throttling

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Theorem 7.1 (Sparse Throttling Equilibria).** Exact second-price throttling equilibrium
computation is FIXP-complete under SL reductions, and approximating the participation vector in
distance to an exact equilibrium is FIXPa-complete; there are finite sets of positive rational bids
and budgets such that both hold already on the instances with at most four positive bids per
bidder, three per good, a common tie priority, and positive bids and budgets in those sets. -/
theorem theorem_7_1 :
    FIXPComplete (throttlingProblemOn (fun _ => True)) ∧
    FIXPaComplete (StrongApprox (throttlingProblemOn (fun _ => True))
      (throttlingProblemOn (fun _ => True)).dim) ∧
    ∃ Bids Budgets : Finset ℚ, (∀ q ∈ Bids, 0 < q) ∧ (∀ q ∈ Budgets, 0 < q) ∧
      FIXPComplete (throttlingProblemOn (ThrottleData.Sparse Bids Budgets)) ∧
      FIXPaComplete (StrongApprox (throttlingProblemOn (ThrottleData.Sparse Bids Budgets))
        (throttlingProblemOn (ThrottleData.Sparse Bids Budgets)).dim) := by sorry

end ExactAutobid.Equilibria
