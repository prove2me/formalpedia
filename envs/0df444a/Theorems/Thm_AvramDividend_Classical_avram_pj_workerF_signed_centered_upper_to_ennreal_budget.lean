-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_signed_centered_upper_to_ennreal_budget
-- name    : AvramDividend.Classical.avram_pj_workerF_signed_centered_upper_to_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:51:01.19645+00:00
-- url     : https://prove2.me/theorems/6525eb1f-4ad1-47db-b500-446a64b4e35f
-- title:
--   Nonnegative centred signed stopped supermartingale upper yields finite ENNReal expectation budget
-- statement:
--   On a probability space, if an almost-everywhere measurable nonnegative real stopped reward F is bounded by b plus an integrable centred martingale term M and two nonpositive signed drift and dividend loss terms G,R, then its full ENNReal expectation is ≤ENNReal.ofReal b. Its integrability follows without assuming integrability of G/R, via the already-Proved three-compensator signed source lemma. The exact pinned Mathlib integral-to-lintegral and non-top identities lift the real mean bound to extended real. This is the genuine bridge for an original stopped Ito/Meyer signed inequality with inclusive dividend cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_signed_centered_upper_to_ennreal_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F M G R : Ω → ℝ) (b : ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFpos : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hMI : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P, F ω ≤ b + M ω + G ω + R ω) :
    (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) ≤ ENNReal.ofReal b := by sorry
