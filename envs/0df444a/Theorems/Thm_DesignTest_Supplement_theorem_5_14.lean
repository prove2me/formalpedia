-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_14
-- name    : DesignTest.Supplement.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:14:41.530929+00:00
-- url     : https://prove2.me/theorems/7b2bacaa-37eb-4cd7-8f0a-47f2f02242ad
-- title:
--   Theorem 5.14 — Tolerant sample lower bound for unitary 1-designs
-- statement:
--   There is a universal constant $c_0>0$ such that for $d\ge2$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le c_0$ and $\delta_{\mathrm{fail}}\in[0,1/3]$, every $(1,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT tester using at most $m$ samples in every execution satisfies
--
--   $$m=\Omega\Big(\frac d{\varepsilon_{\mathrm{far}}^2}+\frac{d^2}{\log d}\Big(\frac{\varepsilon_{\mathrm{apx}}}{\varepsilon_{\mathrm{far}}^2}+\frac{\varepsilon_{\mathrm{apx}}^2}{\varepsilon_{\mathrm{far}}^4}\Big)\Big)\qquad(112),$$
--
--   with a universal implicit constant and the natural logarithm. The bound holds even with classical-description access; all inputs in the reduction have finite support.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: a lower bound for every tester correct on all promised inputs, with the printed clause that the hard YES and NO distributions have finite support → the bound for every tester correct on the finitely supported promised inputs (IsFinSupp ν in the YES and NO hypotheses); reason: encodes the printed finite-support clause; a tester correct on all promised inputs is in particular correct on these, so the source's bound is the special case
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.14, p.67 (PDF p.70)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.14** (Tolerant sample lower bound for unitary 1-designs). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.14, eq. (112), p.67.

There is a universal constant `c₀ > 0` such that, for `d ≥ 2`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, c₀]` and
`δ_fail ∈ [0, 1/3]`, every `(1, ε_apx, ε_far, δ_fail)`-UDT tester using at most `m` samples in every execution
satisfies `m = Ω(d/ε_far² + d²/log d · (ε_apx/ε_far² + ε_apx²/ε_far⁴))`. The bound holds even in the
classical-description access model; all inputs used in the reduction have finite support.

**Formalization Note.** `c₀` and the universal `Ω` constant `c` are chosen first; `log` is natural. Testers
as in Theorem 5.7. -/
theorem theorem_5_14 :
    ∃ c₀ c : ℝ, 0 < c₀ ∧ 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ c₀ → 0 ≤ δ → δ ≤ 1 / 3 → ∀ H : Measure (U d), IsHaarProb H →
      ∀ (m : ℕ) (f : (Fin m → U d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
        twirlDist 1 H ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
        εfar < twirlDist 1 H ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      c * ((d : ℝ) / εfar ^ 2 + (d : ℝ) ^ 2 / Real.log d *
        (εapx / εfar ^ 2 + εapx ^ 2 / εfar ^ 4)) ≤ (m : ℝ) := by sorry

end DesignTest.Supplement
