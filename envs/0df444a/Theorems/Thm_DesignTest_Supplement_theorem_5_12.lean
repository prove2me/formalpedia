-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_12
-- name    : DesignTest.Supplement.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:13:53.359963+00:00
-- url     : https://prove2.me/theorems/12eb9d1a-499b-49ac-ad88-a63bde112377
-- title:
--   Theorem 5.12 — UDT on the known Weyl support ($t=1$): non-adaptive incoherent tester, $q_{\mathrm{total}}=2m$
-- statement:
--   Let $t=1$, $d\ge2$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1$, $\delta_{\mathrm{fail}}\in(0,1/2)$, $\gamma_{\mathrm{gap}}=\varepsilon_{\mathrm{far}}-\varepsilon_{\mathrm{apx}}$. Suppose each sampled oracle is, up to global phase, one of the Weyl matrices $X^aZ^b$ ($X|k\rangle=|k+1\bmod d\rangle$, $Z|k\rangle=e^{2\pi ik/d}|k\rangle$). For the $(1,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT promise on this support there is a non-adaptive incoherent tester in the uncontrolled unitary access model with $q_{\mathrm{total}}=2m$ and
--
--   1. $m=O(d^2\gamma_{\mathrm{gap}}^{-2}\log(1/\delta_{\mathrm{fail}}))$;
--   2. for $\varepsilon_{\mathrm{apx}}=0$, $m=O(d\,\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}}))$ (109);
--   3. for a universal $c>0$, if $\varepsilon_{\mathrm{far}}\le1/2$ and $\varepsilon_{\mathrm{apx}}\le c\varepsilon_{\mathrm{far}}$,
--   $$m=O\Big(\Big[\frac d{\varepsilon_{\mathrm{far}}^2}+\frac{d^2\varepsilon_{\mathrm{apx}}}{\varepsilon_{\mathrm{far}}^2}+\frac{d^2\varepsilon_{\mathrm{apx}}^2}{\varepsilon_{\mathrm{far}}^4}\Big]\log\frac1{\delta_{\mathrm{fail}}}\Big)\qquad(110).$$
--
--   Every query uses a new input and is immediately measured.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: each sampled oracle is, up to phase, in the known set → ν-almost every sample lies in the phase-closed set; reason: same instances
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.12, p.65-66 (PDF p.68-69)

import Mathlib
import Definitions.Def_DesignTest_Supplement_UNAI
import Definitions.Def_DesignTest_Supplement_weylSet

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.12** (UDT on the Weyl support). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.12, eqs. (109)–(110), pp.65–66.

Let `t = 1`, `d ≥ 2`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`, `γ_gap = ε_far − ε_apx`.
Suppose each sampled oracle is, up to global phase, one of the known Weyl matrices `X^a Z^b`. There is a
non-adaptive incoherent tester in the uncontrolled unitary access model for the `(1, ε_apx, ε_far, δ_fail)`-UDT
promise on this support with `q_total = 2m` and
(1) `m = O(d²/γ_gap² · log(1/δ_fail))`;
(2) for the exact YES promise `ε_apx = 0`, `m = O(d/ε_far² · log(1/δ_fail))` (109);
(3) for a universal constant `c > 0`, if `ε_far ≤ 1/2` and `ε_apx ≤ c ε_far`,
`m = O([d/ε_far² + d² ε_apx/ε_far² + d² ε_apx²/ε_far⁴] log(1/δ_fail))` (110).
Every query uses a new input and is immediately measured.

**Formalization Note.** One `O` constant `C` and the universal `c` are chosen first. "Each sampled oracle is
one of the Weyl matrices up to phase" is `ν`-almost every sample lying in `weylUpToPhase d`; YES and NO
are the UDT promises restricted to such `ν`. The tester (`UNAIProc d m (2m) w K`) may use this knowledge. -/
theorem theorem_5_12 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 → 0 < δ → δ < 1 / 2 → ∀ H : Measure (U d), IsHaarProb H →
      (∃ m : ℕ, (m : ℝ) ≤ C * (d : ℝ) ^ 2 / (εfar - εapx) ^ 2 * Real.log (1 / δ) ∧
          ∃ (w K : ℕ) (T : UNAIProc d m (2 * m) w K), T.IsTester ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              twirlDist 1 H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              εfar < twirlDist 1 H ν → T.acceptProb ν ≤ δ)) ∧
      (εapx = 0 → ∃ m : ℕ, (m : ℝ) ≤ C * (d : ℝ) / εfar ^ 2 * Real.log (1 / δ) ∧
          ∃ (w K : ℕ) (T : UNAIProc d m (2 * m) w K), T.IsTester ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              twirlDist 1 H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              εfar < twirlDist 1 H ν → T.acceptProb ν ≤ δ)) ∧
      (εfar ≤ 1 / 2 → εapx ≤ c * εfar →
        ∃ m : ℕ, (m : ℝ) ≤ C * ((d : ℝ) / εfar ^ 2 + (d : ℝ) ^ 2 * εapx / εfar ^ 2 +
            (d : ℝ) ^ 2 * εapx ^ 2 / εfar ^ 4) * Real.log (1 / δ) ∧
          ∃ (w K : ℕ) (T : UNAIProc d m (2 * m) w K), T.IsTester ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              twirlDist 1 H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ weylUpToPhase d) →
              εfar < twirlDist 1 H ν → T.acceptProb ν ≤ δ)) := by sorry

end DesignTest.Supplement
