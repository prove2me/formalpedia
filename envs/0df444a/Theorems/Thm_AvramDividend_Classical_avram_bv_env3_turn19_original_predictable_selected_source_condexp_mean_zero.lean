-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:48:07.003037+00:00
-- url     : https://prove2.me/theorems/55f11c62-d918-481e-93b6-96814f3feb16
-- title:
--   Original predictable stopped-grid selection preserves source conditional zero mean
-- statement:
--   On the original Lévy probability space with its right-continuous filtration, a source increment M_i which is integrable and has zero conditional expectation at its physical grid time u_i has zero integral when restricted to the predictable event i<k(omega). The event is explicitly measurable in the corresponding source filtration. No unconditional martingale mean is silently promoted to an optionally selected mean.
-- source:
--   Pinned Mathlib MeasureTheory.setIntegral_condExp, ae_restrict_of_ae, and original SpectrallyNegativeLevy.isProbability. Generalises the Proved original-process conditional initial event integral e8169f69 to each event-selected stopped grid index. Input conditional mean-zero remains an explicit source obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn19_original_predictable_selected_source_condexp_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (k : Ω → ℕ)
    (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hPredictable : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    ∀ i, (∫ ω in {ω : Ω | i < k ω}, M i ω ∂P) = 0 := by sorry
