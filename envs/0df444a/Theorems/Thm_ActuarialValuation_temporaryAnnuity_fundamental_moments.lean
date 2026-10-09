-- Prove2me | Theorems.Thm_ActuarialValuation_temporaryAnnuity_fundamental_moments
-- name    : ActuarialValuation.temporaryAnnuity_fundamental_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:19:15.638038+00:00
-- url     : https://prove2.me/theorems/bd50b0f2-6efb-4a50-9c95-ca669ae143da
-- title:
--   Fundamental temporary life-annuity moment identities
-- statement:
--   For a finite policy term, the stated mortality model and discount factor, this result collects the expected values, second moments and variances for both payment timings. The moment identities are finite algebraic results and do not assert a whole-life theorem.
--
--   **Mathematical statement**
--
--   $$
--   \begin{aligned}\mathbb E[Z_{\mathrm{due}}]&=\sum_{k<n}v^kP(S_k)\\\mathbb E[Z_{\mathrm{immediate}}]&=\sum_{k<n}v^{k+1}P(S_{k+1})\\\operatorname{Var}(Z_\bullet)&=\mathbb E[Z_\bullet^2]-\mathbb E[Z_\bullet]^2\end{aligned}
--   $$
-- source:
--   Source equations (3.15)–(3.16) and derived moments from (3.5)–(3.6), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
open MeasureTheory

namespace ActuarialValuation

theorem temporaryAnnuity_fundamental_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ((∫ ω, temporaryAnnuityDuePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal)
    ∧ ((∫ ω, temporaryAnnuityImmediatePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)
    ∧ ((∫ ω, (temporaryAnnuityDuePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal)
    ∧ ((∫ ω, (temporaryAnnuityImmediatePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal)
    ∧ (ProbabilityTheory.variance (temporaryAnnuityDuePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal) ^ 2)
    ∧ (ProbabilityTheory.variance (temporaryAnnuityImmediatePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal) ^ 2) := by sorry

end ActuarialValuation
