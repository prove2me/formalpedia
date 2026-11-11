-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_4_1
-- name    : ExactAutobid.Equilibria.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:58.405449+00:00
-- url     : https://prove2.me/theorems/43ea11b7-7e54-47be-b5e9-5f3ce261ffc7
-- title:
--   Theorem 4.1 — second-price ROI pacing is FIXP-complete (and FIXPa-complete) for every fixed rational cap A > 1
-- statement:
--   For every fixed rational cap $A > 1$, finding an exact second-price ROI pacing equilibrium $(\alpha, x)$ is **FIXP-complete under SL reductions**, and approximating the multiplier vector $\alpha$ within a supplied rational $\varepsilon > 0$ in $\ell_\infty$ of some exact equilibrium is **FIXPa-complete**. Moreover there is a finite set $V_A \subset \mathbb{Q}_{>0}$, depending only on $A$, such that both statements hold already on the markets with at most four positive valuations per bidder, at most two per good, and all positive valuations in $V_A$:
--   $$\forall A \in \mathbb{Q}_{>1}:\; \mathrm{FIXPComplete}(\Pi_A) \wedge \mathrm{FIXPaComplete}(\Pi_A^{\approx}) \wedge \exists V_A\; \big(\mathrm{FIXPComplete}(\Pi_A|_{V_A}) \wedge \mathrm{FIXPaComplete}(\Pi_A|_{V_A}^{\approx})\big).$$
--
--   This is part (i) of Theorem 1.1, settling the completeness question left open by FHHH24's membership result.
--
--   Differences from the source:
--   - reading: exact equilibrium computation (solution = equilibrium) → the solution vector is (α, x) ∈ ℝ^{n + n|J|}, multipliers first; reason: Definition 2.1 defines the equilibrium as the pair (α, x)
--   - reading: every fixed rational cap A > 1 → the cap is a parameter of the problem (one real search problem per A), machines may depend on A; reason: 'fixed' cap
--   - reading: hardness holds with at most four positive valuations per bidder, two per good, positive valuations in a fixed finite set depending only on A → ∃ V_A (finite, positive) after A and before the instance, with FIXPComplete and FIXPaComplete of the problem restricted to PacingData.Sparse V_A; reason: restriction constants quantified before the instance; completeness on the class includes its (inherited) membership
--   - encoding: approximating the control vector within a supplied rational ε > 0 in ℓ∞ of some exact equilibrium → StrongApprox P k: instances (I, ε) with rational ε > 0, answers rational lists of length k(I) within ε of the first k(I) coordinates of some y ∈ Sol(I); reason: the controls are the first coordinates of every solution vector of this mission
--   - reading: FIXPa (reduction notion not spelled out in the paper; [EY10]) → InFIXPa D := polynomial-time search reduction (instance map f, answer map g, every answer of f(I) mapped to an answer of I) from D to StrongApprox basicFIXP (whole fixed point); FIXPa-hard/complete accordingly; reason: EY10's definition of FIXPa through polynomial-time search reductions; the paper uses it without restating it
--   - encoding: polynomial time (binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime on framed binary encodings over the four-letter alphabet Sym, as in the published FixpReciprocal_SLReduces; reason: Lean convention already fixed by the reused FIXP framework; every rational is written in binary
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 12 (PDF 14), Theorem 4.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_ExactAutobid_Equilibria_FIXPa
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing

open FixpReciprocal

namespace ExactAutobid.Equilibria

/-- **Theorem 4.1 (Every Nontrivial Fixed Cap Is Hard).** For every fixed rational cap `A > 1`,
exact second-price ROI pacing equilibrium computation is FIXP-complete under SL reductions, and
approximating the multiplier vector in distance to an exact equilibrium is FIXPa-complete; there is
a finite set `V_A` of positive rationals such that both hold already on the instances with at most
four positive valuations per bidder, two per good, and all positive valuations in `V_A`. -/
theorem theorem_4_1 (A : ℚ) (hA : 1 < A) :
    FIXPComplete (roiPacingProblem A) ∧
    FIXPaComplete (StrongApprox (roiPacingProblem A) (pacingControls A (fun _ => True))) ∧
    ∃ V : Finset ℚ, (∀ q ∈ V, 0 < q) ∧
      FIXPComplete (roiPacingProblemOn A (PacingData.Sparse V)) ∧
      FIXPaComplete (StrongApprox (roiPacingProblemOn A (PacingData.Sparse V))
        (pacingControls A (PacingData.Sparse V))) := by sorry

end ExactAutobid.Equilibria
