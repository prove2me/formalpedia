-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_variance
-- name    : ActuarialValuation.temporaryAnnuityDue_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:13:43.139981+00:00
-- url     : https://prove2.me/theorems/6de174f8-7571-4403-b32c-2d58092021f2
-- title:
--   Variance of the temporary annuity in advance
-- statement:
--   The variance is the annuity-due second moment less the square of its expected present value. The second moment retains the dependence between payments through their overlapping survival events.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(Z_{\mathrm{due}})=\mathbb E[Z_{\mathrm{due}}^2]-\mathbb E[Z_{\mathrm{due}}]^2
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.1.1, equations (3.5)–(3.6), and §3.3.2, equations (3.15)–(3.16), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuityDue_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (temporaryAnnuityDuePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal) ^ 2 := by sorry

end ActuarialValuation
