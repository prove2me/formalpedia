-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_9
-- name    : DesignTest.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:13:24.728203+00:00
-- url     : https://prove2.me/theorems/45f24df7-6345-4f93-a5b7-332f85cd1cc0
-- title:
--   Theorem 5.9 — Query lower bound for UDT: $q_{\mathrm{total}}=\Omega_t(\Delta^{1/3}d^{2t/3}\max\{1,(\Delta/\varepsilon_{\mathrm{far}}^2)^{1/3}\})$
-- statement:
--   Fix $t\ge1$. Let $d\ge t$, $\varepsilon_{\mathrm{far}}\in(0,1/4]$, $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\delta_{\mathrm{fail}}\in[0,1/2)$, $\Delta=1-2\delta_{\mathrm{fail}}$, $N=d^t\binom dt$, and assume $N\ge640/\Delta$ (90). Every $(t,\varepsilon_{\mathrm{apx}},\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-UDT tester that uses at most $q_{\mathrm{total}}$ queries in every execution satisfies
--
--   $$q_{\mathrm{total}}=\Omega_t\Big(\Delta^{1/3}d^{2t/3}\max\Big\{1,\Big(\frac{\Delta}{\varepsilon_{\mathrm{far}}^2}\Big)^{1/3}\Big\}\Big)\qquad(91),$$
--
--   regardless of the number of samples, even for adaptive coherent testers with controlled access to both $C_U$ and $C_U^\dagger$. The hard YES and NO distributions have finite support.
--
--   **Formalization Note.** Testers are randomized adaptive coherent controlled-access algorithms with any number of samples, any workspace and any instrument sizes; they are required to be correct only on finitely supported inputs.
--
--   Differences from the source:
--   - encoding: O_t(·) / Ω_t(·) → a constant depending only on t, chosen before d and the accuracy parameters; reason: the theorem lets these constants depend on t only
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
--   - encoding: a lower bound for every tester correct on all promised inputs, with the printed clause that the hard YES and NO distributions have finite support → the bound for every tester correct on the finitely supported promised inputs (IsFinSupp ν in the YES and NO hypotheses); reason: encodes the printed finite-support clause; a tester correct on all promised inputs is in particular correct on these, so the source's bound is the special case
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.9, p.56 (PDF p.59)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_CAC

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.9** (Query lower bound for UDT). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.9, eqs. (90)–(91), p.56.

Fix `t ≥ 1`. Let `d ≥ t`, `ε_far ∈ (0, 1/4]`, `ε_apx ∈ [0, ε_far)`, `δ_fail ∈ [0, 1/2)`; put
`Δ := 1 − 2δ_fail`, `N := d^t C(d, t)` and assume `N ≥ 640/Δ` (90). Every `(t, ε_apx, ε_far, δ_fail)`-UDT tester
using at most `q_total` queries in every execution satisfies
`q_total = Ω_t(Δ^{1/3} d^{2t/3} max{1, (Δ/ε_far²)^{1/3}})` (91), regardless of the number of samples, even for
adaptive coherent testers with controlled access to both `C_U` and `C_U†`. The hard YES and NO distributions
have finite support.

**Formalization Note.** `Ω_t`: a constant `c > 0` depending only on `t`, chosen before `d` and the other
parameters. Testers are `CACProc d m q w K J` (every `m`, workspace `w`, instrument sizes), the most
general class (p.16); `q` bounds the calls in every execution. Correctness is only required on finitely
supported inputs, as the theorem's hard instances are. -/
theorem theorem_5_9 (t : ℕ) (ht : 1 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, t ≤ d → ∀ εfar εapx δ : ℝ, 0 < εfar → εfar ≤ 1 / 4 → 0 ≤ εapx →
      εapx < εfar → 0 ≤ δ → δ < 1 / 2 →
      (640 : ℝ) / (1 - 2 * δ) ≤ ((d ^ t * Nat.choose d t : ℕ) : ℝ) →
      ∀ H : Measure (U d), IsHaarProb H →
      ∀ (m q w K J : ℕ) (T : CACProc d m q w K J), T.IsTester →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
          twirlDist t H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) →
        (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], IsFinSupp ν →
          εfar < twirlDist t H ν → T.acceptProb ν ≤ δ) →
        c * (1 - 2 * δ) ^ ((1 : ℝ) / 3) * (d : ℝ) ^ ((2 * t : ℝ) / 3) *
          max 1 (((1 - 2 * δ) / εfar ^ 2) ^ ((1 : ℝ) / 3)) ≤ (q : ℝ) := by sorry

end DesignTest.Supplement
