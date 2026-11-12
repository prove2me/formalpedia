-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_contact_safe_masked_sequence_upper
-- name    : AvramDividend.Classical.avram_bvb_b21_contact_safe_masked_sequence_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:57:30.169492+00:00
-- url     : https://prove2.me/theorems/9dd9d26c-8cf1-413e-94b1-460e6694f8aa
-- title:
--   Contact-safe one-sided bound for masked convergent samples
-- statement:
--   A within-cap continuous nonnegative loss admits a one-sided eventual bound along every convergent sampling sequence, even if the sequence leaves the cap arbitrarily often; outside-cap samples contribute zero.
-- source:
--   Contact-safe original marked-loss pointwise upper limsup route for phys95 and later-ruin genuine-grid sampling.

import Mathlib
open Classical Filter Set
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_contact_safe_masked_sequence_upper
    {α : Type*} [TopologicalSpace α]
    (s : Set α) (x : α) (f : α → ℝ)
    (hcont : ContinuousWithinAt f s x) (hnonneg : 0 ≤ f x)
    (seq : ℕ → α) (hseq : Tendsto seq atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (if seq n ∈ s then f (seq n) else 0) ≤ f x + ε := by sorry
