-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_5_1
-- name    : ExactAutobid.Equilibria.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:32.801257+00:00
-- url     : https://prove2.me/theorems/c2581b32-8f40-4636-8fa6-0745ab27a949
-- title:
--   Theorem 5.1 — budget-constrained no-self-pricing GSP is FIXP-complete (and FIXPa-complete)
-- statement:
--   Finding an exact budget-constrained no-self-pricing GSP equilibrium is **FIXP-complete under SL reductions**, and approximating the multiplier vector in distance to an exact equilibrium is **FIXPa-complete**. There is a universal constant $c$ such that both hold already on single auctions with unit click-through rates, full display, positive rational values and budgets, and at most $c$ goods per bidder; on that class, finding the multipliers together with an equilibrium distribution over legal orders of polynomial support is also FIXP-complete:
--   $$\mathrm{FIXPComplete}(\Pi_B) \wedge \mathrm{FIXPaComplete}(\Pi_B^{\approx}) \wedge \exists c\, \big(\mathrm{FIXPComplete}(\Pi_B|_c) \wedge \mathrm{FIXPaComplete}(\Pi_B|_c^{\approx}) \wedge \exists p\; \mathrm{FIXPComplete}(\Pi_B|_c^{\le p})\big).$$
--
--   This is part (ii) of Theorem 1.1, answering the open question of DLPST26 for the budget model.
--
--   Differences from the source:
--   - reading: GSP auctions (bidders with catalogs of positive values, CTRs, budgets) → the published Auction.ValidFor standing assumptions of [HLN26]: nonempty catalogs listed by nonincreasing positive value, 1 ≤ K ≤ M, CTRs in (0, 1] nonincreasing; positive budgets (budget model) or none (ROI model); reason: the paper takes its GSP model and FIXP membership from [HLN26]; the hard instances (K = M, unit CTRs) satisfy them
--   - reading: an equilibrium (α, π) with π a distribution over legal tied orders → the solution vector is α; α is a solution iff some distribution π over orders valid at α makes (α, π) an equilibrium; reason: π ranges over M! orders and cannot be a coordinate block of fixed dimension; [HLN26] and the published ABERealSearch make the same choice
--   - reading: hardness holds in one auction with unit CTRs, full display, positive rational values and budgets, a universal constant bound on goods per bidder → ∃ c before the instance, with FIXPComplete and FIXPaComplete of the problem restricted to UnitFullBounded c (K = number of goods, all CTRs 1, ≤ c goods per bidder); reason: constant quantified before the instance
--   - reading: hardness holds ... with polynomial-support equilibrium distributions over legal tied orders → ∃ polynomial p with FIXPComplete of the restricted problem whose solutions α carry an equilibrium π supported on at most p(|enc I|) orders; reason: the clause describes the equilibria of the hard instances; stated as completeness of the support-bounded variant on the restricted class
--   - encoding: approximating the control vector within a supplied rational ε > 0 in ℓ∞ of some exact equilibrium → StrongApprox P k: instances (I, ε) with rational ε > 0, answers rational lists of length k(I) within ε of the first k(I) coordinates of some y ∈ Sol(I); reason: the controls are the first coordinates of every solution vector of this mission
--   - reading: FIXPa (reduction notion not spelled out in the paper; [EY10]) → InFIXPa D := polynomial-time search reduction (instance map f, answer map g, every answer of f(I) mapped to an answer of I) from D to StrongApprox basicFIXP (whole fixed point); FIXPa-hard/complete accordingly; reason: EY10's definition of FIXPa through polynomial-time search reductions; the paper uses it without restating it
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 20 (PDF 22), Theorem 5.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_FIXPa
import Definitions.Def_ExactAutobid_Equilibria_GSP

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Theorem 5.1 (Exact Budget-Constrained GSP Equilibria).** Exact budget-constrained
no-self-pricing GSP equilibrium computation is FIXP-complete under SL reductions, and approximating
the multiplier vector in distance to an exact equilibrium is FIXPa-complete; there is a universal
constant `c` such that both hold already on single auctions with unit CTRs, full display, positive
rational values and budgets and at most `c` goods per bidder, and there finding the multipliers
together with an equilibrium distribution of polynomial support over legal orders is
FIXP-complete. -/
theorem theorem_5_1 :
    FIXPComplete (budgetGSPProblemOn (fun _ => True)) ∧
    FIXPaComplete (StrongApprox (budgetGSPProblemOn (fun _ => True))
      (budgetGSPProblemOn (fun _ => True)).dim) ∧
    ∃ c : ℕ,
      FIXPComplete (budgetGSPProblemOn (UnitFullBounded c)) ∧
      FIXPaComplete (StrongApprox (budgetGSPProblemOn (UnitFullBounded c))
        (budgetGSPProblemOn (UnitFullBounded c)).dim) ∧
      ∃ p : Polynomial ℕ,
        FIXPComplete (gspSuppProblemOn (fun Au => BudgetInstance Au ∧ UnitFullBounded c Au)
          budgetEq p) := by sorry

end ExactAutobid.Equilibria
