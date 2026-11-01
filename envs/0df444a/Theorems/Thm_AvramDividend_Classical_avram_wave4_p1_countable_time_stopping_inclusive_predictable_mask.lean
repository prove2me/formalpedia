-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
-- name    : AvramDividend.Classical.avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:43:32.82166+00:00
-- url     : https://prove2.me/theorems/c3d85546-8351-4a29-93ec-6e68240f1788
-- title:
--   Inclusive stopped survival mask predictable for countably right-separated time orders
-- statement:
--   For an actual adapted filtration over a linearly ordered time type and a stopping time τ, assume the time order admits a countable subset D with a separator between a and b whenever a<b. Prove the inclusive time-stop mask { (t,ω) : t≤τ(ω) } is measurable in the actual filtration predictable sigma algebra. It covers continuous nonnegative real time by rational D and discrete time by natural D. For each s∈D, the event {t≤s}∪({t>s}∩{τ>s}) is predictable because {τ>s} is F_s measurable by the original stopping time property; the inclusive mask is the countable intersection of these events, proved using the separator hypothesis. This is not the compensation identity or a martingale conclusion, and does not assume an intensity.
-- source:
--   Pinned Mathlib Probability.Process.Stopping IsStoppingTime, Probability.Process.Predictable measurableSet_predictable_Ioi_prod; MeasureTheory.MeasurableSpace.Defs MeasurableSet.biInter. Elementary linearly ordered separation.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (D : Set ι) (hD : D.Countable)
    (hSep : ∀ a b : ι, a < b →
      ∃ s : ι, s ∈ D ∧ a ≤ s ∧ s < b)
    (τ : Ω → ι)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι))) :
    MeasurableSet[𝓕.predictable]
      {p : ι × Ω | p.1 ≤ τ p.2} := by sorry
