-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_13
-- name    : DesignTest.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:14:18.085068+00:00
-- url     : https://prove2.me/theorems/e8b5ee4e-6b36-43fe-92e7-4e82e6c69499
-- title:
--   Theorem 5.13 — Sample lower bound for unitary 1-design testing: $m\ge(1-2\delta_{\mathrm{fail}})d/(43\varepsilon_{\mathrm{far}}^2)$
-- statement:
--   Let $d\ge2$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1/4$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. Every tester for $(1,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT using at most $m$ samples in every execution satisfies
--
--   $$m\ \ge\ \frac{(1-2\delta_{\mathrm{fail}})\,d}{43\,\varepsilon_{\mathrm{far}}^2}\qquad(111).$$
--
--   The bound holds even with classical-description access; both YES and NO distributions have finite support.
--
--   Differences from the source:
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: a lower bound for every tester correct on all promised inputs, with the printed clause that the hard YES and NO distributions have finite support → the bound for every tester correct on the finitely supported promised inputs (IsFinSupp ν in the YES and NO hypotheses); reason: encodes the printed finite-support clause; a tester correct on all promised inputs is in particular correct on these, so the source's bound is the special case
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.13, p.66 (PDF p.69)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.13** (Sample lower bound for unitary 1-design testing). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.13, eq. (111), p.66.

Let `d ≥ 2`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ [0, 1/2)`. Every tester for
`(1, ε_apx, ε_far, δ_fail)`-UDT using at most `m` samples in every execution satisfies
`m ≥ (1 − 2δ_fail) d/(43 ε_far²)`. The bound holds even in the classical-description access model
(Definition 3.9); both YES and NO distributions have finite support.

**Formalization Note.** As in Theorem 5.7: a measurable `f : U(d)^m → [0, 1]`, correct on finitely supported
inputs. -/
theorem theorem_5_13 (d : ℕ) (hd : 2 ≤ d) (εapx εfar δ : ℝ) (ha0 : 0 ≤ εapx) (haf : εapx < εfar)
    (hf4 : εfar ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (H : Measure (U d)) (hH : IsHaarProb H)
    (m : ℕ) (f : (Fin m → U d) → ℝ) (hfmeas : Measurable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hyes : ∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
      twirlDist 1 H ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν))
    (hno : ∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
      εfar < twirlDist 1 H ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) :
    (1 - 2 * δ) * (d : ℝ) / (43 * εfar ^ 2) ≤ (m : ℝ) := by sorry

end DesignTest.Supplement
