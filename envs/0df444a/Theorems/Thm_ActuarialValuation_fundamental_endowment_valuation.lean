-- Prove2me | Theorems.Thm_ActuarialValuation_fundamental_endowment_valuation
-- name    : ActuarialValuation.fundamental_endowment_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T20:01:06.98425+00:00
-- url     : https://prove2.me/theorems/97d65573-cc93-41bc-b539-2051bea3e2f5
-- title:
--   Fundamental valuation identities for pure and endowment assurances
-- statement:
--   This result gathers the strict exact-lifetime pure-endowment moments and the endowment assurance valuation and moments. It also relates strict survival beyond the term to curtate survival to maturity by accounting for deaths exactly at maturity.
--
--   **Mathematical statement**
--
--   $$
--   \begin{aligned}E_n^\ge&=E_n^>\cup\{T=n\}\\ \mathbb E[Z_{\mathrm{pure}}]&=v^nP(T>n)\\ \mathbb E[Z_{\mathrm{endow}}]&=\sum_{k=0}^{n-1}v^{k+1}P(K=k)+v^nP(K\ge n)\end{aligned}
--   $$
-- source:
--   Derived capstone of equations (3.9) and (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_pureEndowmentPV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation

theorem fundamental_endowment_valuation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (K : Ω → ℕ) (hK : Measurable K)
    (hKT : ∀ ω, (K ω : ℝ) ≤ T ω ∧ T ω < (K ω : ℝ) + 1) (v : ℝ) (n : ℕ)
    : ((strictSurvivalEvent T n) ∪ {ω | T ω = (n : ℝ)} = (curtateSurvivalEvent K n))
    ∧ ((∫ ω, pureEndowmentPV T v n ω ∂P) = v ^ n * (P (strictSurvivalEvent T n)).toReal)
    ∧ (ProbabilityTheory.variance (pureEndowmentPV T v n) P = (v ^ n) ^ 2 * (P (strictSurvivalEvent T n)).toReal * (1 - (P (strictSurvivalEvent T n)).toReal))
    ∧ (∀ ω, endowmentAssurancePV K v n ω = termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω)
    ∧ ((∫ ω, endowmentAssurancePV K v n ω ∂P) = (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal)
    ∧ ((∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) = (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal)
    ∧ (ProbabilityTheory.variance (endowmentAssurancePV K v n) P = ((∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal) - ((∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal) ^ 2) := by sorry

end ActuarialValuation
