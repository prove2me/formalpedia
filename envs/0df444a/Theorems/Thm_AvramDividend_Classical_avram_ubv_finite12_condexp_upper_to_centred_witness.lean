-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_condexp_upper_to_centred_witness
-- name    : AvramDividend.Classical.avram_ubv_finite12_condexp_upper_to_centred_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T08:17:36.460253+00:00
-- url     : https://prove2.me/theorems/c80460e8-e947-4663-94bf-1543252acddc
-- title:
--   An initial conditional budget yields a conditionally centred integrable domination witness
-- statement:
--   An integrable real-valued stopped reward F whose conditional expectation under the right-continuous initial filtration is almost everywhere at most b admits an integrable witness M with zero initial conditional expectation and F at most b+M almost everywhere. Use the residual F minus its initial conditional expectation and the already-Proved initial-event orthogonality lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_condexp_upper_to_centred_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F : Ω → ℝ) (hFI : Integrable F P)
    (hCondUpper : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b) :
    ∃ M : Ω → ℝ, Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ b + M ω) := by sorry
