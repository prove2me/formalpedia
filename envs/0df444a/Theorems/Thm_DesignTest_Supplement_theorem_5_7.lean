-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_7
-- name    : DesignTest.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:12:34.308069+00:00
-- url     : https://prove2.me/theorems/c29f0081-c7ed-4253-b940-bd13eb206799
-- title:
--   Theorem 5.7 — Sample lower bound for UDT: $m\ge\sqrt{2(1-2\delta_{\mathrm{fail}})\lfloor d^t\binom dt/2\rfloor}/(2\varepsilon_{\mathrm{far}})$
-- statement:
--   Fix $t\ge1$. Let $d\ge\max\{2,t\}$, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}<1/2$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. Every $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT tester that uses at most $m$ samples in every execution satisfies
--
--   $$m\ \ge\ \frac{\sqrt{2(1-2\delta_{\mathrm{fail}})\lfloor d^t\binom dt/2\rfloor}}{2\varepsilon_{\mathrm{far}}}=\Omega_t\Big(\frac{\sqrt{1-2\delta_{\mathrm{fail}}}\,d^t}{\varepsilon_{\mathrm{far}}}\Big).$$
--
--   The bound holds even when the tester receives the full matrices of the samples (classical-description access), hence in every black-box access model and for any number of queries; the hard YES and NO distributions have finite support.
--
--   **Formalization Note.** The tester is a measurable $f:U(d)^m\to[0,1]$ required to be correct only on finitely supported inputs.
--
--   Differences from the source:
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: a lower bound for every tester correct on all promised inputs, with the printed clause that the hard YES and NO distributions have finite support → the bound for every tester correct on the finitely supported promised inputs (IsFinSupp ν in the YES and NO hypotheses); reason: encodes the printed finite-support clause; a tester correct on all promised inputs is in particular correct on these, so the source's bound is the special case
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.7, p.53 (PDF p.56)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.7** (Sample lower bound for UDT). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.7, p.53.

Fix `t ≥ 1`. Let `d ≥ max{2, t}`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/2)`, `δ_fail ∈ [0, 1/2)`. Every
`(t, ε_apx, ε_far, δ_fail)`-UDT tester using at most `m` samples in every execution satisfies
`m ≥ √(2(1 − 2δ_fail)⌊d^t C(d, t)/2⌋)/(2ε_far)`. This holds even in the classical-description access model (Definition 3.9), and the hard YES and NO
distributions have finite support.

**Formalization Note.** A classical-description algorithm with at most `m` samples is a measurable
`f : U(d)^m → [0, 1]` (Definition 3.9: samples may be drawn in advance; the full matrices, phases included,
are given; every black-box access model is simulated). The tester is only required to be correct on
finitely supported inputs (`IsFinSupp`), which is the paper's "hard distributions have finite support"
and makes the bound apply to every tester correct on all promised inputs. `⌊·/2⌋` is natural-number division. -/
theorem theorem_5_7 (t : ℕ) (ht : 1 ≤ t) (d : ℕ) (hd : 2 ≤ d) (hdt : t ≤ d) (εapx εfar δ : ℝ)
    (ha0 : 0 ≤ εapx) (haf : εapx < εfar) (hf2 : εfar < 1 / 2) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2)
    (H : Measure (U d)) (hH : IsHaarProb H) (m : ℕ)
    (f : (Fin m → U d) → ℝ) (hfmeas : Measurable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hyes : ∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
      twirlDist t H ν ≤ εapx → 1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν))
    (hno : ∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
      εfar < twirlDist t H ν → ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ) :
    Real.sqrt (2 * (1 - 2 * δ) * ((d ^ t * Nat.choose d t / 2 : ℕ) : ℝ)) / (2 * εfar) ≤ (m : ℝ) := by sorry

end DesignTest.Supplement
