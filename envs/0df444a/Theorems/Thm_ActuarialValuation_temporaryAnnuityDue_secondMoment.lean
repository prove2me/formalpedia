-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_secondMoment
-- name    : ActuarialValuation.temporaryAnnuityDue_secondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:12:38.104108+00:00
-- url     : https://prove2.me/theorems/d5d8e2d4-be0f-45e0-846a-a50db6be62b5
-- title:
--   Second moment of the temporary annuity in advance
-- statement:
--   The second moment sums over all ordered pairs of annuity-due payments, including pairs with equal payment times. Each pair is discounted by both payment factors and weighted by the probability of survival to the later payment time, as in the general moment theory of equations 3.5 and 3.6.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[Z_{\mathrm{due}}^2]=\sum_{i,j=0}^{n-1}v^{i+j}P(K\ge\max(i,j))
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.1.1, equations (3.5)–(3.6), and §3.3.2, equations (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityDue_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, (temporaryAnnuityDuePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal := by sorry

end ActuarialValuation
