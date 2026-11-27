-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_Supplement_theorem_5_counterexample
-- name    : BleedFeed.ControlLimit.Supplement.theorem_5_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:08:58.35878+00:00
-- url     : https://prove2.me/theorems/4b9be6c7-d8fb-4be2-8182-f16528daab9e
-- title:
--   Theorem 5 (corrected: counterexample to sufficiency of Condition (8))
-- statement:
--   The exact printed Condition (8) does not imply the stated optimality. Take $m_0=\tau=N=1$, $I=2$, $\tilde m=3/2$, $\mathcal M=[1,2]$, $G=(\delta_1+\delta_2)/2$ and
--   $$\nu(m)=1-\frac1{1+18\max(m-3/2,0)}.$$
--   The standing assumptions, Condition (8) for every rate in the entire interval, and even Condition (4) hold. Every rate in the interval has critical age one. The state $(1,2,0)$ lies in the theorem's required domain but satisfies
--   $$C(1,2,0)=6>\frac{11}{2}=B(0),\qquad\neg\operatorname{BleedOpt}(1,2,0).$$
--   Thus bleed–feed is strictly suboptimal at a state covered by Theorem 5. This counterexample retains the inclusive endpoint in the condition's sum and averages only the final term in its denominator. It does not assume a terminal-age conclusion or impose any of Conditions (4), (5) or Assumption 1 as a premise.
--
--   Differences from the source:
--   - correction: under Condition (8), bleed–feed is optimal at every postcritical age before I for every rate and n<N → a concrete admissible instance satisfies Condition (8) on the entire rate interval and Condition (4), yet has C(1,2,0)=6>B(0)=11/2; reason: PDF pp. 40–41 mix rewards at a fixed rate with expectations over a new rate; the exact two-atom witness and full-interval inequality in DISPROOF.md refute the claimed implication without adding premises
--   - encoding: the §3 bleed–feed model and its standing conventions → the immutable published Params, Standing and Bellman recursion; reason: the supplement reuses the existing model; its probability, measurability, positivity and critical-biomass boundary conventions remain unchanged
--   - encoding: a general rate law on the interval and the printed inclusive sum in Condition (8) → the counterexample uses half Dirac mass at each endpoint of [1,2], and Condition8 retains its full interval quantifiers and inclusive finite sum; reason: a two-atom law is an admissible instance; it refutes the universal theorem rather than replacing it with a deterministic special-case theorem
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f3359aaff884b6a5f15444a500c2372a3139920a35d2b3e56cfa43906), p. 20 (PDF 20), Theorem 5 and Condition (8); pp. 40–41, proof of Theorem 5

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Supplement_Condition8

open scoped ENNReal

namespace BleedFeed.ControlLimit.Supplement

/-- Counterexample to Theorem 5 under its exact Condition (8), throughout the whole
    rate interval [1,2]. The failure occurs at the valid terminal decision age. -/
theorem theorem_5_counterexample :
    let P : Params := {
      m0 := 1, tau := 1, muL := 1, muU := 2, mtil := 3 / 2,
      nu := fun m => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹,
      I := 2, N := 1,
      G := (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 1 +
        (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac 2 }
    P.Standing ∧ Condition8 P ∧ Condition4 P ∧
      (∀ μ ∈ P.rates, critAge P μ = 1) ∧
      (2 : ℝ) ∈ P.rates ∧ 1 < P.I ∧ 0 < P.N ∧
      C P 1 2 0 = 6 ∧ B P 0 = 11 / 2 ∧ ¬ BleedOpt P 1 2 0 := by sorry

end BleedFeed.ControlLimit.Supplement
