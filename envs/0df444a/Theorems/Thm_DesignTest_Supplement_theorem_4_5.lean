-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_4_5
-- name    : DesignTest.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:10:17.00323+00:00
-- url     : https://prove2.me/theorems/355c0b2c-0503-4bcf-9c90-f9228b41094f
-- title:
--   Theorem 4.5 — Tolerant state-design tester with per-sample measurements
-- statement:
--   Let $d\ge2$, $t\ge1$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1$, $\delta_{\mathrm{fail}}\in(0,1/2)$ and $\gamma_{\mathrm{gap}}=\varepsilon_{\mathrm{far}}-\varepsilon_{\mathrm{apx}}$. Tolerant $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT (accept $\mathrm{Dist}_1^{(t)}(H,\nu)\le\varepsilon_{\mathrm{apx}}$, reject $>\varepsilon_{\mathrm{far}}$) is solved by a non-adaptive coherent tester with
--
--   $$m=O\Big(\frac{D_{\mathrm{Sym}}}{\gamma_{\mathrm{gap}}^2}\log\frac1{\delta_{\mathrm{fail}}}\Big),\qquad q=O\Big(\frac{td}{\gamma_{\mathrm{gap}}^2}\Big)\ \text{queries per sample},$$
--
--   hence $q_{\mathrm{total}}=mq=O(tdD_{\mathrm{Sym}}\gamma_{\mathrm{gap}}^{-4}\log(1/\delta_{\mathrm{fail}}))$. Each quantum measurement acts jointly only on the copies of one sampled state; outcomes of different samples are combined classically.
--
--   It handles every positive tolerance gap.
--
--   **Formalization Note.** One constant bounds (41) and (42); (43) follows.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.5, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_Supplement_stateProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- **Theorem 4.5** (Tolerant upper bound). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.5, eqs. (41)–(43), p.32.

Let `d ≥ 2`, `t ≥ 1`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`, `γ_gap = ε_far − ε_apx`.
Tolerant `(t, ε_apx, ε_far, δ_fail)`-SDT is solved by a non-adaptive coherent tester with
`m = O(D_Sym/γ_gap² · log(1/δ_fail))` samples and `q = O(t d/γ_gap²)` queries per sample, whose quantum
measurements each act jointly only on the copies of one sampled process, the outcomes of different
processes being combined classically.

**Formalization Note.** One constant `C` before all parameters for (41) and (42); (43),
`q_total = m q = O(t d D_Sym/γ_gap⁴ · log(1/δ_fail))`, follows with constant `C²`. The tester is a
randomized `SPerSampleProc`. -/
theorem theorem_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∃ m q : ℕ, (m : ℝ) ≤ C * (DSym d t : ℝ) / (εfar - εapx) ^ 2 * Real.log (1 / δ) ∧
        (q : ℝ) ≤ C * (t : ℝ) * (d : ℝ) / (εfar - εapx) ^ 2 ∧
        ∃ (K : ℕ) (T : SPerSampleProc d m q K), T.IsTester ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              momentDist t (haarState d) ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              εfar < momentDist t (haarState d) ν → T.acceptProb ν ≤ δ) := by sorry

end DesignTest.Supplement
