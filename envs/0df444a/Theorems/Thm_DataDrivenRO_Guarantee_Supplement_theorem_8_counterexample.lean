-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_Supplement_theorem_8_counterexample
-- name    : DataDrivenRO.Guarantee.Supplement.theorem_8_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:49:39.454098+00:00
-- url     : https://prove2.me/theorems/6e45d10b-d9cc-4b7a-829e-d82b4aed2beb
-- title:
--   Theorem 8 (corrected: counterexample to printed (31) and its guarantee)
-- statement:
--   Let $d=N=1$, $P=\tfrac14\delta_0+\tfrac34\delta_{4/3}$, $g=g_\sigma=1$, and let the fixed sample be zero. At $\epsilon=1/2$, the printed LCX set $U$ is nonempty, compact and convex, but
--   $$
--   U=[-1,1],\qquad \delta^*(1\mid U)=1<4/3=\operatorname{VaR}^P_{1/2}(1),\qquad P\in\mathcal P^{LCX}.
--   $$
--   Consequently $U$ does not imply the probabilistic guarantee. There is also a direct sampling contradiction: under one draw from $P$, the confidence region covers $P$ with probability one, while the probability that the printed family simultaneously implies a guarantee is at most $3/4$. In particular, the advertised confidence level fails for $\alpha=1/8$ despite full coverage.
--
--   This explicit counterexample replaces the false conjunction in Theorem 8; it does not assert that each individual equality in (32) is separately false. The original minimum program is retained in the verbatim milestone and discussed in DISPROOF.md. The source proof on ec7 suggests multiplying the additive threshold in (31b) by $z$; no unverified global repair is asserted here.
--
--   Differences from the source:
--   - correction: Theorem 8 asserts the guarantee and the equality of support, worst-case VaR and (32) → an explicit counterexample to that conjunction, with full-coverage sampling failure and a strict support/VaR gap; reason: PDF 22 prints g once in (31b); with the stated data, the affine constraint u−1≤0 fails with probability 3/4; the missing z factor is exposed by the dual rescaling on PDF 45
--   - reading: the confidence phrase is omitted in Theorem 8 → the counterexample also uses the coverage-based probabilistic reading of Theorem 3; reason: the proof invokes Theorem 3 on PDF 45; coverage is 1 but success is at most 3/4
--   - encoding: probability laws on real vectors and a product sampling law → Fin 1 vectors and samples with explicit Dirac mixtures and Measure.pi; reason: these are exactly the one-dimensional, one-observation instances; support is certified compact and nonempty, and VaR is at an interior level
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 8, (30)–(32), p. 22; EC.1.6, pp. ec6–ec7 (PDF 44–45)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Supplement_LCX

open MeasureTheory
open scoped ENNReal

namespace DataDrivenRO.Guarantee.Supplement

/-- Theorem 8 is false for the set (31) as printed. The confidence region covers the
true law with probability one, but the simultaneous guarantee fails with probability
at least 1/4. The fixed sample zero also contradicts the support/worst-VaR equality. -/
theorem theorem_8_counterexample :
    let P : Measure (Fin 1 → ℝ) :=
      (1 / 4 : ℝ≥0∞) • Measure.dirac (fun _ => 0) +
      (3 / 4 : ℝ≥0∞) • Measure.dirac (fun _ => (4 / 3 : ℝ))
    let S0 : Fin 1 → (Fin 1 → ℝ) := fun _ _ => 0
    let U := ULCXPrinted S0 1 (1 / 2)
    IsProbabilityMeasure P ∧
    P ∈ regionLCX S0 1 1 ∧
    U = {u | -(1 : ℝ) ≤ u 0 ∧ u 0 ≤ 1} ∧
    U.Nonempty ∧ IsCompact U ∧ Convex ℝ U ∧
    RobustMDP.Shared.supportFunction U (fun _ => 1) = 1 ∧
    DataDrivenRO.Guarantee.VaR P (1 / 2) (fun _ => 1) = 4 / 3 ∧
    ¬ DataDrivenRO.Guarantee.ImpliesGuarantee P U (1 / 2) ∧
    (Measure.pi (fun _ : Fin 1 => P)) {S | P ∈ regionLCX S 1 1} = 1 ∧
    (Measure.pi (fun _ : Fin 1 => P))
      {S | DataDrivenRO.Guarantee.SimultaneouslyImpliesGuarantee P
        (fun ε => ULCXPrinted S 1 ε)} ≤ (3 / 4 : ℝ≥0∞) := by sorry

end DataDrivenRO.Guarantee.Supplement
