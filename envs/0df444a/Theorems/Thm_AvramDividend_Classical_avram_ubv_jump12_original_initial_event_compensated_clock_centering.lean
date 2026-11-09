-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_compensated_clock_centering
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_initial_event_compensated_clock_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:26:19.405947+00:00
-- url     : https://prove2.me/theorems/eb05cecc-2635-4181-bcc6-1ef494183478
-- title:
--   Original compensated negative-jump stopped source remains centred on every initial event
-- statement:
--   For the literal original sample-path negative jump-count measure and real-time negative-mark compensator, assume the same stopped compensated source is integrable and mean zero for every right-continuous stopping clock. Then it has zero integral restricted to any initial event. The conclusion follows by masking the clock, the exact count/compensator null-at-zero identities, and the original stopping-time mask lemma.
-- source:
--   Direct source-exact eventwise stochastic centring bridge needed to use canonical original compensated Taylor mean-zero 7061d3d7 in the original positive-clock reward budget 0b1a879a-c9c5-4d2c-9039-a143ec7db5dc. This interface intentionally assumes only the separately Proved all-clock centring, not a physical Ito dividend ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_initial_event_masked_stop
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_jump_integral
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_compensator
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump12_original_initial_event_compensated_clock_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (H : Ω → (ℝ≥0 × ℝ) → ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then H ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then H ω (t, z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    (∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)) →
      Integrable (J ρ) P ∧ (∫ ω, J ρ ω ∂P) = 0) →
    (∫ ω in A, J σ ω ∂P) = 0 := by sorry
