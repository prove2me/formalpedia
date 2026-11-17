-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_5
-- name    : DesignTest.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:11:54.843803+00:00
-- url     : https://prove2.me/theorems/a0e0d586-19f7-4442-bea1-782d195a032b
-- title:
--   Theorem 5.5 — Tolerant UDT by single-query tomography: non-adaptive incoherent tester
-- statement:
--   Let $d\ge2$, $t\ge1$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1$, $\delta_{\mathrm{fail}}\in(0,1/2)$, $\gamma_{\mathrm{gap}}=\varepsilon_{\mathrm{far}}-\varepsilon_{\mathrm{apx}}$. There is a non-adaptive incoherent tester in the uncontrolled unitary access model solving $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT with
--
--   $$m=\Big\lceil\frac{64d^{2t}}{\gamma_{\mathrm{gap}}^2}\log\frac{4d^{2t}}{\delta_{\mathrm{fail}}}\Big\rceil\ \text{samples},\qquad q=O\Big(\frac{t^2d^2}{\gamma_{\mathrm{gap}}^2}\log\frac m{\delta_{\mathrm{fail}}}\Big)\ \text{queries per sampled oracle},$$
--
--   so $q_{\mathrm{total}}=mq$. Every query uses a new $d$-dimensional input without a reference register and is measured individually; neither controlled nor inverse queries are used.
--
--   The tester handles every positive gap, at the price of more queries per sample than Theorem 5.4.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.5, p.48-49 (PDF p.51-52)

import Mathlib
import Definitions.Def_DesignTest_Supplement_UNAI

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.5** (Non-adaptive incoherent tolerant tester in the uncontrolled unitary access model for
UDT). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.5, eqs. (77)–(78), pp.48–49.

Let `d ≥ 2`, `t ≥ 1`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`, `γ_gap = ε_far − ε_apx`.
A non-adaptive incoherent tester in the uncontrolled unitary access model solves
`(t, ε_apx, ε_far, δ_fail)`-UDT with `m = ⌈64 d^{2t}/γ_gap² · log(4 d^{2t}/δ_fail)⌉` independent samples and
`q = O(t² d²/γ_gap² · log(m/δ_fail))` queries per sampled oracle (`q_total = m q`). Every query uses a new
`d`-dimensional input without a reference register, followed by an individual measurement; neither
controlled nor inverse queries are used.

**Formalization Note.** `UNAIProc d m n 1 K`: reference dimension `w = 1` (no reference), every call forward
(`σ = true`), each sample queried at most `q` times (so `n ≤ m q`). The `O` constant `C` is chosen first. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 → 0 < δ → δ < 1 / 2 → ∀ H : Measure (U d), IsHaarProb H →
      ∃ m : ℕ, m = ⌈64 * (d : ℝ) ^ (2 * t) / (εfar - εapx) ^ 2 *
          Real.log (4 * (d : ℝ) ^ (2 * t) / δ)⌉₊ ∧
        ∃ q : ℕ, (q : ℝ) ≤ C * (t : ℝ) ^ 2 * (d : ℝ) ^ 2 / (εfar - εapx) ^ 2 * Real.log (m / δ) ∧
          ∃ (n K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧
            (∀ ω i, (T.alg ω).queriesTo i ≤ q) ∧ (∀ ω j, (T.alg ω).σ j = true) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], twirlDist t H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], εfar < twirlDist t H ν → T.acceptProb ν ≤ δ) := by sorry

end DesignTest.Supplement
