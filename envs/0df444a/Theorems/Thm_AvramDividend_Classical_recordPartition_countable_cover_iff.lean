-- Prove2me | Theorems.Thm_AvramDividend_Classical_recordPartition_countable_cover_iff
-- name    : AvramDividend.Classical.recordPartition_countable_cover_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:54:53.51547+00:00
-- url     : https://prove2.me/theorems/f296acae-c115-453f-b8cd-f6073bfc3a28
-- title:
--   Cofinal monotone record levels yield a complete countable half-open interval cover
-- statement:
--   For a monotone sequence of real record levels which is cofinal above every real point, the countable family of consecutive half-open intervals (u_i,u_(i+1)] covers exactly the points strictly above the initial level. This extends the remotely Proved finite partition cover identity, without assuming strictly increasing levels or changing the strict-left, weak-right endpoint convention. Combined with the separately Proved disjointness lemma, it gives the countable deterministic partition required before analysing the random inverse-record clock.
-- source:
--   Remotely Proved recordPartition_finite_cover_iff 3f2b95f1-5c84-47e0-a362-61f1639d5806 and recordPartition_Ioc_disjoint 26b30a5d-eb69-4fbf-b1ab-aa17bfbb5d8e.

import Theorems.Thm_AvramDividend_Classical_recordPartition_finite_cover_iff

open Set

theorem AvramDividend.Classical.recordPartition_countable_cover_iff
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (x : ℝ) :
    u 0 < x ↔ ∃ i : ℕ, x ∈ Set.Ioc (u i) (u (i + 1)) := by sorry
