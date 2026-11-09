-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_sampled_ceiling_is_true_physical_stop
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_ceiling_is_true_physical_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:19:49.29228+00:00
-- url     : https://prove2.me/theorems/c0152114-2c3f-468c-8d21-0a1746a8eda7
-- title:
--   A genuine sampled-filtration stopping index gives a genuine physical right-continuous stopping clock
-- statement:
--   Source-faithful interface for Avram original-process Gaussian C² reward consumers a338c453-58c0-411c-aaca-5cec689ed807 and 249c532d-4ec0-498c-81f0-b380dd476344. If a monotone physical grid samples the original right-continuous filtration, and K is a true stopping index for that sampled filtration, then e(K) is a stopping time for the original physical-time filtration. This converts the Proved arbitrary-clock ceiling index 604909b0 into a legal argument for the Proved stopped Gaussian source and conditional identities 4a4b4e27 and 6242d57f. The theorem does not assume that flooring an arbitrary clock preserves stopping times; it does not establish the subsequent quadratic L1 source limit or controlled dividend ledger.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_ceiling_is_true_physical_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (e (K ω) : WithTop ℝ≥0)) := by
  sorry
