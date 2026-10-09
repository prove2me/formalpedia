-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_secondMoment
-- name    : ActuarialValuation.temporaryAnnuityImmediate_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:13:12.344969+00:00
-- url     : https://prove2.me/theorems/f216871b-a928-42fc-85f9-cf62dff32edf
-- title:
--   Second moment of the temporary annuity in arrears
-- statement:
--   The second moment sums over all ordered pairs of end-year annuity-immediate payments, including pairs with equal payment dates. Each pair is weighted by the probability of survival to the later payment date, as in the general moment theory of equations 3.5 and 3.6.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{immediate}}^2]=\sum_{i,j=0}^{n-1}v^{i+j+2}P(K\ge\max(i+1,j+1))
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.1.1, equations (3.5)–(3.6), and §3.3.2, equations (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityImmediate_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, (temporaryAnnuityImmediatePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal := by sorry

end ActuarialValuation
