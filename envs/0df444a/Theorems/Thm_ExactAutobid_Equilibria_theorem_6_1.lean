-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_6_1
-- name    : ExactAutobid.Equilibria.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:39.9072+00:00
-- url     : https://prove2.me/theorems/29b504cb-357f-4eb0-b40c-8c28b9679823
-- title:
--   Theorem 6.1 — ROI-constrained no-self-pricing GSP is FIXP-complete (and FIXPa-complete) for the canonical cap and every prescribed cap A > 1
-- statement:
--   For the canonical instance-defined cap $A_0 = 1 + \sum v / \min v$, and for every prescribed fixed rational cap $A > 1$, finding an exact ROI-constrained no-self-pricing GSP equilibrium is **FIXP-complete under SL reductions**, and approximating the multiplier vector in distance is **FIXPa-complete**. Both hold already on single auctions with unit CTRs, full display, positive rational values and at most $c$ goods per bidder, where $c$ is universal for the canonical cap and depends only on $A$ for a prescribed cap; on that class finding the multipliers together with an equilibrium distribution over legal orders of polynomial support is also FIXP-complete:
--   $$\big(\mathrm{FC}(\Pi_{A_0}) \wedge \mathrm{FaC}(\Pi_{A_0}^{\approx}) \wedge \exists c\,(\dots)\big) \wedge \forall A \in \mathbb{Q}_{>1}\; \big(\mathrm{FC}(\Pi_{A}) \wedge \mathrm{FaC}(\Pi_{A}^{\approx}) \wedge \exists c_A\,(\dots)\big).$$
--
--   This is part (iii) of Theorem 1.1.
--
--   Differences from the source:
--   - reading: GSP auctions (bidders with catalogs of positive values, CTRs, budgets) → the published Auction.ValidFor standing assumptions of [HLN26]: nonempty catalogs listed by nonincreasing positive value, 1 ≤ K ≤ M, CTRs in (0, 1] nonincreasing; positive budgets (budget model) or none (ROI model); reason: the paper takes its GSP model and FIXP membership from [HLN26]; the hard instances (K = M, unit CTRs) satisfy them
--   - reading: an equilibrium (α, π) with π a distribution over legal tied orders → the solution vector is α; α is a solution iff some distribution π over orders valid at α makes (α, π) an equilibrium; reason: π ranges over M! orders and cannot be a coordinate block of fixed dimension; [HLN26] and the published ABERealSearch make the same choice
--   - reading: the canonical instance-defined cap or any prescribed fixed rational cap A > 1 → the canonical cap is the published capA0 computed from the instance (IsApproxABER at γ = 0); a prescribed cap is a parameter of the problem (IsROIGSPEqCap with cap A); reason: two cap conventions of §2.1
--   - reading: a constant bound on goods per bidder, universal for the canonical cap and depending only on A otherwise → ∃ c before the instance for the canonical cap; ∀ A > 1, ∃ c after A and before the instance; reason: constant placement
--   - reading: hardness holds ... with polynomial-support equilibrium distributions over legal tied orders → ∃ polynomial p with FIXPComplete of the restricted problem whose solutions α carry an equilibrium π supported on at most p(|enc I|) orders; reason: the clause describes the equilibria of the hard instances; stated as completeness of the support-bounded variant on the restricted class
--   - encoding: approximating the control vector within a supplied rational ε > 0 in ℓ∞ of some exact equilibrium → StrongApprox P k: instances (I, ε) with rational ε > 0, answers rational lists of length k(I) within ε of the first k(I) coordinates of some y ∈ Sol(I); reason: the controls are the first coordinates of every solution vector of this mission
--   - reading: FIXPa (reduction notion not spelled out in the paper; [EY10]) → InFIXPa D := polynomial-time search reduction (instance map f, answer map g, every answer of f(I) mapped to an answer of I) from D to StrongApprox basicFIXP (whole fixed point); FIXPa-hard/complete accordingly; reason: EY10's definition of FIXPa through polynomial-time search reductions; the paper uses it without restating it
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), pp. 29–30 (PDF 31–32), Theorem 6.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_FIXPa
import Definitions.Def_ExactAutobid_Equilibria_GSP

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Theorem 6.1 (Exact ROI-Constrained GSP Equilibria).** For the canonical instance-defined cap
and for every prescribed fixed rational cap `A > 1`, exact ROI-constrained no-self-pricing GSP
equilibrium computation is FIXP-complete under SL reductions and approximating the multiplier
vector in distance is FIXPa-complete; both hold already on single auctions with unit CTRs, full
display, positive rational values and at most `c` goods per bidder, with `c` universal for the
canonical cap and depending only on `A` otherwise, where finding the multipliers together with an
equilibrium distribution of polynomial support over legal orders is FIXP-complete. -/
theorem theorem_6_1 :
    (FIXPComplete (roiGSPCanonicalProblemOn (fun _ => True)) ∧
      FIXPaComplete (StrongApprox (roiGSPCanonicalProblemOn (fun _ => True))
        (roiGSPCanonicalProblemOn (fun _ => True)).dim) ∧
      ∃ c : ℕ,
        FIXPComplete (roiGSPCanonicalProblemOn (UnitFullBounded c)) ∧
        FIXPaComplete (StrongApprox (roiGSPCanonicalProblemOn (UnitFullBounded c))
          (roiGSPCanonicalProblemOn (UnitFullBounded c)).dim) ∧
        ∃ p : Polynomial ℕ,
          FIXPComplete (gspSuppProblemOn (fun Au => ROIInstance Au ∧ UnitFullBounded c Au)
            roiCanonicalEq p)) ∧
    ∀ A : ℚ, 1 < A →
      FIXPComplete (roiGSPCapProblemOn A (fun _ => True)) ∧
      FIXPaComplete (StrongApprox (roiGSPCapProblemOn A (fun _ => True))
        (roiGSPCapProblemOn A (fun _ => True)).dim) ∧
      ∃ c : ℕ,
        FIXPComplete (roiGSPCapProblemOn A (UnitFullBounded c)) ∧
        FIXPaComplete (StrongApprox (roiGSPCapProblemOn A (UnitFullBounded c))
          (roiGSPCapProblemOn A (UnitFullBounded c)).dim) ∧
        ∃ p : Polynomial ℕ,
          FIXPComplete (gspSuppProblemOn (fun Au => ROIInstance Au ∧ UnitFullBounded c Au)
            (fun Au α π => IsROIGSPEqCap Au (A : ℝ) α π) p) := by sorry

end ExactAutobid.Equilibria
