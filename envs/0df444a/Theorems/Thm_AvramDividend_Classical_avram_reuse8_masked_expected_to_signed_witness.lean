-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_reuse8_masked_expected_to_signed_witness
-- name    : AvramDividend.Classical.avram_reuse8_masked_expected_to_signed_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:40:53.189447+00:00
-- url     : https://prove2.me/theorems/82b7f95a-47a7-48e9-bfd2-9528ee435ca2
-- title:
--   A nonpositive expected zero-masked payoff admits a five-part signed witness
-- statement:
--   For a probability space and a family of right-continuous-filtration stopping times, if each nonnegative integrable payoff has expected zero-masked reward at most its initial budget, it admits the centred-three-compensator plus nonpositive-two-remainder witness used in the original Avram UBV local verification theorem.
-- source:
--   Source-exact conditional bridge for canonical 6b50f324, using Proved original mask L1 ca595620 and mean centring 817ff85b. Actual stopped reward nonnegativity 5893451b and initial candidate nonnegativity dcc85b03 discharge the bridge inputs. The required expected bound ea12272f remains Open.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Theorems.Thm_AvramDividend_Classical_avram_route10_signed_integrable_nonpositive_mean_centering

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_reuse8_masked_expected_to_signed_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (hb : 0 ≤ b)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hFI : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hExpected : ∀ k,
      (∫ ω, if σ k ω = 0 then b else F k ω ∂P) ≤ b) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      AEStronglyMeasurable (fun ω => if σ k ω = 0 then b else F k ω) P ∧
      (0 ≤ᵐ[P] fun ω => if σ k ω = 0 then b else F k ω) ∧
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then b else F k ω) ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
