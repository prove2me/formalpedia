-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_1_1
-- name    : ExactAutobid.Equilibria.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:22.027299+00:00
-- url     : https://prove2.me/theorems/2cd80e38-e2b3-4b9a-a1dd-91aef83f47bc
-- title:
--   Theorem 1.1 — exact second-price ROI pacing, budget- and ROI-constrained GSP, and second-price throttling equilibria are FIXP-complete
-- statement:
--   The following equilibrium-computation problems are **FIXP-complete under separable linear reductions**, and remain so on the stated restricted classes, every restriction constant being fixed before the instance:
--
--   (i) second-price ROI pacing, for every fixed rational cap $A > 1$, and on the markets with at most two interested bidders per good, at most four goods per bidder and all positive valuations in a finite set $V_A \subset \mathbb{Q}_{>0}$ depending only on $A$;
--
--   (ii) budget-constrained no-self-pricing GSP, and on single auctions with full display, unit CTRs, positive rational values and budgets and at most $c$ goods per bidder, $c$ universal;
--
--   (iii) ROI-constrained no-self-pricing GSP with the canonical instance-defined cap ($c$ universal) and with every prescribed fixed rational cap $A > 1$ ($c$ depending only on $A$), on the same kind of auctions;
--
--   (iv) second-price throttling, and on the markets with at most three positive bids per good, at most four goods with a positive bid per bidder, a common tie priority, and bids and budgets in fixed finite sets of positive rationals.
--
--   $$\Big(\forall A>1:\ \mathrm{FC}(\Pi^{\mathrm{ROI}}_A) \wedge \exists V_A\ \mathrm{FC}(\Pi^{\mathrm{ROI}}_A|_{V_A})\Big) \wedge \Big(\mathrm{FC}(\Pi_B) \wedge \exists c\ \mathrm{FC}(\Pi_B|_c)\Big) \wedge \Big(\mathrm{FC}(\Pi_{A_0}) \wedge \exists c\ \mathrm{FC}(\Pi_{A_0}|_c) \wedge \forall A>1\ (\mathrm{FC}(\Pi_A) \wedge \exists c_A\ \mathrm{FC}(\Pi_A|_{c_A}))\Big) \wedge \Big(\mathrm{FC}(\Pi_T) \wedge \exists \mathcal{B},\mathcal{W}\ \mathrm{FC}(\Pi_T|_{\mathcal{B},\mathcal{W}})\Big).$$
--
--   The theorem settles the complexity of exact equilibria for the three autobidding models whose FIXP membership was known (FHHH24, HLN26, CKK22).
--
--   Differences from the source:
--   - reading: equilibrium-computation problems (solutions) → solution vectors: (α, x) for ROI pacing; α with some equilibrium distribution π over valid orders for GSP; θ for throttling; reason: Definition 2.1 pairs α with x; π over M! orders cannot be fixed-dimension coordinates; Definition 2.4 is in θ alone
--   - reading: hardness holds ... with at most two interested bidders per good, at most four goods per bidder, ... (and the other restrictions) → FIXPComplete of each problem restricted to its class, with V_A, c, c(A) and the finite bid/budget sets existentially quantified before the instance; reason: 'hardness holds on the class' together with membership inherited from the general problem
--   - reading: in (ii) and (iii), one auction with full display, unit CTRs, positive rational values, and a distribution over legal tied orders as part of the equilibrium → UnitFullBounded c (K = number of goods, all CTRs 1) on top of the published Auction.ValidFor standing assumptions; the distribution is the ∃ π in the solution set; reason: published GSP model of [HLN26], from which the paper takes it
--   - reading: every fixed rational cap A > 1 (pacing and prescribed-cap ROI-GSP) → the cap is a parameter of the problem, one real search problem per A; reason: 'fixed' cap; Lemma A.1's input-cap variant is a separate statement
--   - encoding: at most four goods per bidder (throttling) → at most four goods with a positive bid per bidder; reason: Theorem 7.1's wording 'four positive bids per bidder'
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 2 (PDF 4), Theorem 1.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing
import Definitions.Def_ExactAutobid_Equilibria_GSP
import Definitions.Def_ExactAutobid_Equilibria_Throttling

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Theorem 1.1 (Exact autobidding equilibria).** The following problems are FIXP-complete under
SL reductions, already on the stated restricted classes: (i) second-price ROI pacing, for every
fixed rational cap `A > 1` (≤ 2 interested bidders per good, ≤ 4 goods per bidder, positive
valuations in a finite set `V_A`); (ii) budget-constrained GSP (unit CTRs, full display, positive
values and budgets, ≤ `c` goods per bidder, `c` universal); (iii) ROI-constrained GSP with the
canonical cap (`c` universal) and with every prescribed rational cap `A > 1` (`c = c(A)`);
(iv) second-price throttling (≤ 3 positive bids per good, ≤ 4 goods per bidder, common priority,
bids and budgets in fixed finite sets). -/
theorem theorem_1_1 :
    (∀ A : ℚ, 1 < A →
      FIXPComplete (roiPacingProblem A) ∧
      ∃ V : Finset ℚ, (∀ q ∈ V, 0 < q) ∧
        FIXPComplete (roiPacingProblemOn A (PacingData.Sparse V))) ∧
    (FIXPComplete (budgetGSPProblemOn (fun _ => True)) ∧
      ∃ c : ℕ, FIXPComplete (budgetGSPProblemOn (UnitFullBounded c))) ∧
    (FIXPComplete (roiGSPCanonicalProblemOn (fun _ => True)) ∧
      (∃ c : ℕ, FIXPComplete (roiGSPCanonicalProblemOn (UnitFullBounded c))) ∧
      ∀ A : ℚ, 1 < A →
        FIXPComplete (roiGSPCapProblemOn A (fun _ => True)) ∧
        ∃ c : ℕ, FIXPComplete (roiGSPCapProblemOn A (UnitFullBounded c))) ∧
    (FIXPComplete (throttlingProblemOn (fun _ => True)) ∧
      ∃ Bids Budgets : Finset ℚ, (∀ q ∈ Bids, 0 < q) ∧ (∀ q ∈ Budgets, 0 < q) ∧
        FIXPComplete (throttlingProblemOn (ThrottleData.Sparse Bids Budgets))) := by sorry

end ExactAutobid.Equilibria
