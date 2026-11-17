-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_19
-- name    : DesignTest.Supplement.theorem_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:15:08.603206+00:00
-- url     : https://prove2.me/theorems/98fa848f-77c5-4977-8b3d-2b0d1907afae
-- title:
--   Theorem 5.19 — Combined sample lower bound for unitary 2-designs in prime-power dimension
-- statement:
--   Let $d\ge4$ be a prime power, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1/4$, $\delta_{\mathrm{fail}}\in[0,1/2)$, $s=1-2\delta_{\mathrm{fail}}$ and $a^*=\min\{1,(d+1)\varepsilon_{\mathrm{apx}}/2\}$. Every $(2,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT tester using at most $m$ samples in every execution satisfies
--
--   $$m=\Omega\Big(\max\Big\{\frac{\sqrt s\,d^2}{\varepsilon_{\mathrm{far}}},\ \frac{s\,d^{3/2}}{\varepsilon_{\mathrm{far}}^2},\ \frac{s\,a^*d^2}{\varepsilon_{\mathrm{far}}^2}\Big\}\Big)\qquad(117),$$
--
--   with a universal implicit constant. The bound holds even with classical-description access; the hard instances have finite support.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: a lower bound for every tester correct on all promised inputs, with the printed clause that the hard YES and NO distributions have finite support → the bound for every tester correct on the finitely supported promised inputs (IsFinSupp ν in the YES and NO hypotheses); reason: encodes the printed finite-support clause; a tester correct on all promised inputs is in particular correct on these, so the source's bound is the special case
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.19, p.71-72 (PDF p.74-75)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.19** (Combined sample lower bound for unitary 2-designs). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.19,
eqs. (116)–(117), pp.71–72.

Let `d ≥ 4` be a prime power, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ [0, 1/2)`; put
`s := 1 − 2δ_fail` and `a* := min{1, (d + 1)ε_apx/2}`. Every `(2, ε_apx, ε_far, δ_fail)`-UDT tester using at most
`m` samples in every execution satisfies `m = Ω(max{√s d²/ε_far, s d^{3/2}/ε_far², s a* d²/ε_far²})`, with a
universal implicit constant. The bound holds even in the classical-description access model; the hard YES
and NO instances have finite support.

**Formalization Note.** The universal constant `c` is chosen first. Testers as in Theorem 5.7. -/
theorem theorem_5_19 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 4 ≤ d → IsPrimePow d → ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar →
      εfar ≤ 1 / 4 → 0 ≤ δ → δ < 1 / 2 → ∀ H : Measure (U d), IsHaarProb H →
      ∀ (m : ℕ) (f : (Fin m → U d) → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
        twirlDist 2 H ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν)) →
      (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
        εfar < twirlDist 2 H ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) →
      c * max (max (Real.sqrt (1 - 2 * δ) * (d : ℝ) ^ 2 / εfar)
          ((1 - 2 * δ) * (d : ℝ) ^ ((3 : ℝ) / 2) / εfar ^ 2))
          ((1 - 2 * δ) * min 1 (((d : ℝ) + 1) * εapx / 2) * (d : ℝ) ^ 2 / εfar ^ 2) ≤ (m : ℝ) := by sorry

end DesignTest.Supplement
