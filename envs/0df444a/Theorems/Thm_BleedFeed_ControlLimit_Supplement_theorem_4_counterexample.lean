-- Prove2me | Theorems.Thm_BleedFeed_ControlLimit_Supplement_theorem_4_counterexample
-- name    : BleedFeed.ControlLimit.Supplement.theorem_4_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:08:30.528377+00:00
-- url     : https://prove2.me/theorems/13897f56-8217-45cf-a66b-3751a2702ee5
-- title:
--   Theorem 4 (corrected: counterexample to the claimed limiting increment)
-- statement:
--   The printed limiting conclusion and Remark 3's proposed repair both fail on the full model domain. Take $m_0=\tau=\mu_\ell=\mu_u=I=1$, $\tilde m=3/2$, $G=\delta_1$ and
--   $$\nu(m)=1-\frac1{1+18\max(m-3/2,0)}.$$
--   This parameter choice satisfies the published standing assumptions and has $\tilde\imath_1=1$, with positive critical age of probability one. Nevertheless, for every natural regulatory limit,
--   $$F_P(N)=1,\qquad\Delta_P(N)=0,\qquad L_P=1.$$
--   Consequently the increments converge neither to $\tilde m=3/2$ nor to $L_P=1$. This is a counterexample to the full universal source result, rather than a claim that its monotonicity and decreasing-increment clauses fail. It also rules out strict readings of “increases” and “decreasing” on the full source domain.
--
--   Differences from the source:
--   - correction: Theorem 4 gives a universal positive-branch limit of critical biomass; Remark 3 replaces it by expected precritical rewards → a concrete admissible counterexample has positive critical age but increments identically zero, different from both proposed limits; reason: PDF pp. 9, 11 and 13 allow I=1 and terminate cultivation at I; the reset also consumes one period (p. 12), so F(N)=1 for every N; DISPROOF.md retains both claims and the exact witness
--   - encoding: the §3 bleed–feed model and its standing conventions → the immutable published Params, Standing and Bellman recursion; reason: the supplement reuses the existing model; its probability, measurability, positivity and critical-biomass boundary conventions remain unchanged
--   - encoding: expected biomass and convergence as the regulatory limit grows → real integrals F, increments and Filter.Tendsto over every natural N with only Params.N updated; reason: all witness integrals are finite Dirac integrals; no finite regulatory range or redefined value function is used
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f3359aaff884b6a5f15444a500c2372a3139920a35d2b3e56cfa43906), p. 18 (PDF 18), Theorem 4 and Remark 3; pp. 36–38, proof; §3 pp. 8–13, especially terminal boundary p. 13

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Supplement_RegulatoryValue

namespace BleedFeed.ControlLimit.Supplement

/-- Counterexample to Theorem 4's printed limit and to Remark 3's proposed repair
    on the full §3 domain: I = 1 allows no further reward before mandatory harvest. -/
theorem theorem_4_counterexample :
    let P : Params := {
      m0 := 1, tau := 1, muL := 1, muU := 1, mtil := 3 / 2,
      nu := fun m => 1 - (1 + 18 * max (m - 3 / 2) 0)⁻¹,
      I := 1, N := 0, G := MeasureTheory.Measure.dirac 1 }
    P.Standing ∧ critAge P 1 = 1 ∧
      P.G {μ | 0 < critAge P μ} = 1 ∧
      (∀ N : ℕ, F P N = 1) ∧ (∀ N : ℕ, increment P N = 0) ∧
      criticalReward P = 1 ∧
      ¬ Filter.Tendsto (increment P) Filter.atTop (nhds P.mtil) ∧
      ¬ Filter.Tendsto (increment P) Filter.atTop (nhds (criticalReward P)) := by sorry

end BleedFeed.ControlLimit.Supplement
