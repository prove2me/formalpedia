-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_4_4
-- name    : DesignTest.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:09:22.794569+00:00
-- url     : https://prove2.me/theorems/54ad7944-b34b-43c3-a73e-be1ee3b0edeb
-- title:
--   Theorem 4.4 — Exact state-design testers with $q=t$ queries per sample
-- statement:
--   Let $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{far}}\in(0,1]$, $\delta_{\mathrm{fail}}\in(0,1/2)$ and $D_{\mathrm{Sym}}=\binom{d+t-1}{t}$. Exact $(t,\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT (accept exact state $t$-designs, reject $\nu$ with $\mathrm{Dist}_1^{(t)}(H,\nu)>\varepsilon_{\mathrm{far}}$) is solved by
--
--   1. a non-adaptive coherent tester with $m=O\big(D_{\mathrm{Sym}}\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}})\big)$ samples (38), and
--   2. an incoherent tester with $m=O_t\big(D_{\mathrm{Sym}}d^{t/2}\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}})\big)$ samples (39);
--
--   both query each sample $t$ times, so $q_{\mathrm{total}}=tm$. Each tester accepts with probability at least $1-\delta_{\mathrm{fail}}$ in the YES case and at most $\delta_{\mathrm{fail}}$ in the NO case.
--
--   Compared with Theorem 4.11, these testers trade more samples for only $t$ queries per sample.
--
--   **Formalization Note.** The coherent tester is the mission's `NACTester d m t`; the incoherent one is a randomized non-adaptive incoherent procedure measuring every copy separately.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: O_t(·) / Ω_t(·) → a constant depending only on t, chosen before d and the accuracy parameters; reason: the theorem lets these constants depend on t only
--   - generalization: an incoherent tester (adaptivity allowed) → a non-adaptive incoherent tester; reason: a non-adaptive incoherent tester is an incoherent tester; the proof's tester fixes all bases in advance
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.4, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_NACTester
import Definitions.Def_DesignTest_Supplement_stateProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- **Theorem 4.4** (Exact testers with few queries per sample). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.4, eqs. (38)–(39), p.31.

Let `d ≥ 2`, `t ≥ 1`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`. Exact `(t, ε_far, δ_fail)`-SDT is solved
(1) by a non-adaptive coherent tester with `m = O(D_Sym/ε_far² · log(1/δ_fail))` samples, and
(2) by an incoherent tester with `m = O_t(D_Sym d^{t/2}/ε_far² · log(1/δ_fail))` samples;
both use `q = t` queries per sample, so `q_total = t m`.

**Formalization Note.** `O(·)` is one constant `C` chosen before all parameters; `O_t(·)` a constant
`C t` depending on `t` only. The coherent tester is the base `NACTester d m t` (a POVM effect on the
`m t` copies). The incoherent tester is a randomized non-adaptive incoherent procedure (`SNAIProc`),
`t` single-copy measurements per sample. YES: `Dist₁^{(t)}(H, ν) = 0`; NO: `> ε_far`. -/
theorem theorem_4_4 :
    (∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εfar δ : ℝ, 0 < εfar → εfar ≤ 1 → 0 < δ →
      δ < 1 / 2 →
      ∃ m : ℕ, (m : ℝ) ≤ C * (DSym d t : ℝ) / εfar ^ 2 * Real.log (1 / δ) ∧
        ∃ T : NACTester d m t,
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              momentDist t (haarState d) ν = 0 → 1 - δ ≤ T.acceptProb ν) ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              εfar < momentDist t (haarState d) ν → T.acceptProb ν ≤ δ)) ∧
    (∃ C : ℕ → ℝ, (∀ t, 0 < C t) ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εfar δ : ℝ, 0 < εfar → εfar ≤ 1 →
      0 < δ → δ < 1 / 2 →
      ∃ m : ℕ, (m : ℝ) ≤ C t * (DSym d t : ℝ) * (d : ℝ) ^ ((t : ℝ) / 2) / εfar ^ 2 * Real.log (1 / δ) ∧
        ∃ (K : ℕ) (T : SNAIProc d m t K), T.IsTester ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              momentDist t (haarState d) ν = 0 → 1 - δ ≤ T.acceptProb ν) ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              εfar < momentDist t (haarState d) ν → T.acceptProb ν ≤ δ)) := by sorry

end DesignTest.Supplement
