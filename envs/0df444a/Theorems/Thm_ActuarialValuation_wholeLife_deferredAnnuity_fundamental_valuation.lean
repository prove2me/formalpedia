-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLife_deferredAnnuity_fundamental_valuation
-- name    : ActuarialValuation.wholeLife_deferredAnnuity_fundamental_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T21:35:51.20792+00:00
-- url     : https://prove2.me/theorems/9d98b78e-e883-44e9-8280-f1e98379e116
-- title:
--   Fundamental whole-life and deferred annuity identities
-- statement:
--   Under the stated probability and discount assumptions, the whole-life annuity-due and annuity-immediate expected present values equal their infinite survival-probability sums, while the deferred expected present values equal the corresponding sums restricted to payment times at or after deferral. For each lifetime outcome, each deferred present value is the matching whole-life present value less its first n possible payments, and the whole-life immediate present value is the whole-life due present value less one. In addition, each deferred expected present value equals the matching whole-life expected present value minus the explicit finite temporary-annuity expected present value.
--
--   **Mathematical statement**
--
--   $$
--   \begin{aligned}{}_{n|}\ddot a&=\ddot a-\ddot a_{\overline n|}\\{}_{n|}a&=a-a_{\overline n|}\\a&=\ddot a-1\end{aligned}
--   $$
-- source:
--   Chapter 3 §3.3.1 eqs (3.11)–(3.12), §3.3.2 eqs (3.15)–(3.16), §3.3.3 eqs (3.17)–(3.18), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem wholeLife_deferredAnnuity_fundamental_valuation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    ((∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) = ∑' k : ℕ, v ^ k * (P (curtateSurvivalEvent K k)).toReal)
    ∧ ((∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) = ∑' k : ℕ, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)
    ∧ ((∫ ω, deferredAnnuityDuePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0)
    ∧ ((∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0)
    ∧ (∀ ω, deferredAnnuityDuePV K v n ω = wholeLifeAnnuityDuePV K v ω - (∑ k ∈ Finset.range n, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω))
    ∧ (∀ ω, deferredAnnuityImmediatePV K v n ω = wholeLifeAnnuityImmediatePV K v ω - (∑ k ∈ Finset.range n, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω))
    ∧ (∀ ω, wholeLifeAnnuityImmediatePV K v ω = wholeLifeAnnuityDuePV K v ω - 1)
    ∧ ((∫ ω, deferredAnnuityDuePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal))
    ∧ ((∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)) := by sorry

end ActuarialValuation
