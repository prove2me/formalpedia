-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_4
-- name    : DesignTest.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:11:30.314197+00:00
-- url     : https://prove2.me/theorems/a6bd85fa-9245-42c3-be1c-074c6dd30241
-- title:
--   Theorem 5.4 — UDT with small tolerance: non-adaptive coherent and incoherent testers, $t$ queries per sample
-- statement:
--   Let $d,t\ge1$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1$, $\delta_{\mathrm{fail}}\in(0,1/2)$. In $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT the tester must accept $\nu$ with $\mathrm{Dist}^{(t)}_\diamond(H,\nu)\le\varepsilon_{\mathrm{apx}}$ and reject $\nu$ with $\mathrm{Dist}^{(t)}_\diamond(H,\nu)>\varepsilon_{\mathrm{far}}$, each with failure probability at most $\delta_{\mathrm{fail}}$. In the uncontrolled unitary access model:
--
--   1. if $\varepsilon_{\mathrm{apx}}\le\varepsilon_{\mathrm{far}}/(2d^{3t/2})$, a non-adaptive coherent tester uses $m=O(d^{3t}\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}}))$ samples and $t$ queries per sample;
--   2. if $\varepsilon_{\mathrm{apx}}\le\kappa_t\varepsilon_{\mathrm{far}}/(2d^{3t/2})$, with $\kappa_t\in(0,1]$ the constant of Lemma 4.3, a non-adaptive incoherent tester uses $m=O_t(d^{4t}\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}}))$ samples and $t$ queries per sample.
--
--   In both cases $q_{\mathrm{total}}=tm$. This includes exact testing ($\varepsilon_{\mathrm{apx}}=0$).
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: O_t(·) / Ω_t(·) → a constant depending only on t, chosen before d and the accuracy parameters; reason: the theorem lets these constants depend on t only
--   - reading: κ_t as in Lemma 4.3 (a constant in (0, 1] depending only on t, built from constants of [CLO22]) → ∃ κ : ℕ → ℝ with 0 < κ t ≤ 1, chosen together with the O_t constant before d and the accuracy parameters; reason: Lemma 4.3 is not part of this supplement and gives κ_t no closed form; the theorem's content is the existence of such a t-only tolerance constant
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.4, p.47 (PDF p.50)

import Mathlib
import Definitions.Def_DesignTest_Supplement_UNAC
import Definitions.Def_DesignTest_Supplement_UNAI

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.4** (Non-adaptive coherent and incoherent testers in the uncontrolled unitary access model
for UDT with small tolerance). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.4, p.47.

Let `d, t ≥ 1`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`. Non-adaptive testers in the
uncontrolled unitary access model solve `(t, ε_apx, ε_far, δ_fail)`-UDT:
(1) if `ε_apx ≤ ε_far/(2 d^{3t/2})`, a coherent tester with `m = O(d^{3t}/ε_far² · log(1/δ_fail))` samples and
`t` queries per sample (`q_total = t m`);
(2) if `ε_apx ≤ κ_t ε_far/(2 d^{3t/2})`, with `κ_t ∈ (0, 1]` the constant of Lemma 4.3, an incoherent tester
with `m = O_t(d^{4t}/ε_far² · log(1/δ_fail))` samples and `t` queries per sample (`q_total = t m`).

**Formalization Note.** `O` is one constant `C` chosen first; `κ_t` and the `O_t` constant are functions of
`t` chosen before `d` and the accuracy parameters. The coherent tester is a `UNACProc` with `t` query slots
per sample; the incoherent one a `UNAIProc` with `t m` experiments and at most (hence exactly) `t` per
sample. `H` is the Haar measure (`IsHaarProb`), the distance `Dist⋄^{(t)}` is `twirlDist`. -/
theorem theorem_5_4 :
    (∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 1 ≤ d → 1 ≤ t → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 → 0 < δ → δ < 1 / 2 → εapx ≤ εfar / (2 * (d : ℝ) ^ ((3 * t : ℝ) / 2)) →
      ∀ H : Measure (U d), IsHaarProb H →
        ∃ m : ℕ, (m : ℝ) ≤ C * (d : ℝ) ^ (3 * t) / εfar ^ 2 * Real.log (1 / δ) ∧
          ∃ (w K : ℕ) (T : UNACProc d m t w K), T.IsTester ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], twirlDist t H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], εfar < twirlDist t H ν → T.acceptProb ν ≤ δ)) ∧
    (∃ κ C : ℕ → ℝ, (∀ t, 0 < κ t ∧ κ t ≤ 1) ∧ (∀ t, 0 < C t) ∧
      ∀ d t : ℕ, 1 ≤ d → 1 ≤ t → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 → 0 < δ → δ < 1 / 2 → εapx ≤ κ t * εfar / (2 * (d : ℝ) ^ ((3 * t : ℝ) / 2)) →
      ∀ H : Measure (U d), IsHaarProb H →
        ∃ m : ℕ, (m : ℝ) ≤ C t * (d : ℝ) ^ (4 * t) / εfar ^ 2 * Real.log (1 / δ) ∧
          ∃ (w K : ℕ) (T : UNAIProc d m (t * m) w K), T.IsTester ∧
            (∀ ω i, (T.alg ω).queriesTo i ≤ t) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], twirlDist t H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], εfar < twirlDist t H ν → T.acceptProb ν ≤ δ)) := by sorry

end DesignTest.Supplement
