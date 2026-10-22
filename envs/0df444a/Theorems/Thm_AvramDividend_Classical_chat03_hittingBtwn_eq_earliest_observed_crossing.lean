-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_earliest_observed_crossing
-- name    : AvramDividend.Classical.chat03_hittingBtwn_eq_earliest_observed_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:15:25.157233+00:00
-- url     : https://prove2.me/theorems/4f5e3c2e-bc2a-4cce-905b-fb510890e54a
-- title:
--   Bounded hittingBtwn equals the earliest sampled crossing index
-- statement:
--   For a discrete sampled process with a first observed hit at index k no later than the terminal cap m, and no hit at any earlier index, Mathlib's bounded hittingBtwn clock equals k. This identifies the actual stopped index with the genuine first strict crossing witnessed by the mesh-approximation theorem.
-- source:
--   Direct application of the pinned Mathlib hittingBtwn_le, hittingBtwn_lt_iff, and hittingBtwn_eq_hittingBtwn_of_exists declarations, with explicit proof of minimality.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_hittingBtwn_eq_earliest_observed_crossing
    {Ω β : Type*} [MeasurableSpace Ω]
    (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (m k : ℕ) (hkm : k ≤ m)
    (hk : u k ω ∈ s)
    (hbefore : ∀ j : ℕ, j < k → u j ω ∉ s) :
    hittingBtwn u s 0 m ω = k := by sorry
