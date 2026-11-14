-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a191_masked_positive_Taylor_small_large_pointwise_split
-- name    : AvramDividend.Classical.avram_ga_a191_masked_positive_Taylor_small_large_pointwise_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:11:03.626024+00:00
-- url     : https://prove2.me/theorems/751ec6c7-abb1-4ad9-b288-07f114667fe5
-- title:
--   Finite masked positive Gaussian physical Taylor sum splits into small squared energy and large-tail source envelope
-- statement:
--   For the real-valued source Taylor remainder on any finite physical mesh with sample-dependent full-cell mask, if the positive part of a small raw-increment cell is bounded by tolerance times its squared increment and the large-cell positive part is bounded by a nonnegative tail envelope, the positive part of the whole masked source sum is bounded by the corresponding weighted finite source energy and large-tail envelope. This uses the Proved finite-sum positive part lemma a25 and is the glue needed in original a149 after source-specific a190 small Taylor and Gaussian tail estimates.
-- source:
--   Proved a25 finite sum max-positive inequality, exact finite pointwise event split.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a25_finite_sum_positive_part_le
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a191_masked_positive_Taylor_small_large_pointwise_split
    {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (r e T : ℕ → Ω → ℝ)
    (ε M δ : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hT : ∀ i ω, 0 ≤ T i ω)
    (hSmall : ∀ i ω, A i ω → |r i ω| < δ →
      max (e i ω) 0 ≤ ε * (r i ω)^2)
    (hLarge : ∀ i ω, A i ω → δ ≤ |r i ω| →
      max (e i ω) 0 ≤ M * T i ω)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then e i ω else 0) 0 ≤
      ε * (∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
      M * (∑ i ∈ S, if A i ω then
        (if δ ≤ |r i ω| then T i ω else 0) else 0) := by sorry
