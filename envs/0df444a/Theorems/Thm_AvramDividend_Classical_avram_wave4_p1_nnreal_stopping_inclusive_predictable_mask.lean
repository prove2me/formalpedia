-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
-- name    : AvramDividend.Classical.avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:02:03.047203+00:00
-- url     : https://prove2.me/theorems/7b40b83c-b7ca-4bf8-9aba-5d91748d538b
-- title:
--   Inclusive stopped mask is predictable on genuine nonnegative real time
-- statement:
--   For the actual controlled source filtration at nonnegative-real time and any finite-valued stopping time τ, prove the inclusive survival mask t≤τ is genuinely predictable with NO additional separability hypothesis. Choose countable D=range(q ↦ Real.toNNReal q) for rational q, use pinned NNReal.lt_iff_exists_rat_btwn for right-separation of every a<b, and apply the generic P1 countably separated stopping theorem. This precise inclusive endpoint is the stopped reserve-dependent kernel nonanticipativity needed for 04-B and Chats03–04; no compensator or martingale conclusion assumed.
-- source:
--   Dependent on countably separated inclusive stopping mask theorem target c3d85546-8351-4a29-93ec-6e68240f1788 being Proved; pinned Mathlib NNReal.lt_iff_exists_rat_btwn and Set.countable_range.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.predictable]
      {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} := by sorry
