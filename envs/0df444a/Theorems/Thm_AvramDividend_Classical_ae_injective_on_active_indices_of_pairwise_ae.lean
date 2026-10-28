-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_injective_on_active_indices_of_pairwise_ae
-- name    : AvramDividend.Classical.ae_injective_on_active_indices_of_pairwise_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:21.020867+00:00
-- url     : https://prove2.me/theorems/9e7b4e2f-da94-43db-b29f-bd0df495eec2
-- title:
--   Countably many random marked arrivals have distinct times simultaneously on their active indices when each active pair is a.s. collision-free
-- statement:
--   A countably indexed Poisson point-family enumeration has random active indices, since each piece k contains K(k,ω) realised marks and unused slots may have duplicate default times. Assume that for each fixed distinct pair of indices i and j, whenever both indices are active their arrival times differ almost surely. Then on one common full-measure set every two simultaneously active indices with equal arrival times are the same index. This handles the random-active-subset issue overlooked by a naively global injectivity theorem and gives exactly the collision-free hypothesis needed for equality of canonical finite-band PRM and intrinsic path jump counts.
-- source:
--   Countable almost-everywhere universal quantifier Mathlib ae_all_iff. Adapted to LeanLevy point-family representation (K:ℕ→Ω→ℕ, X:ℕ→ℕ→Ω→ℝ×ℝ); pairwise null active collisions remain independent stochastic obligation.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.IdentDistrib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_injective_on_active_indices_of_pairwise_ae
    {Ω ι α : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (active : ι → Ω → Prop) (τ : ι → Ω → α)
    (hpair : ∀ i j : ι, i ≠ j →
      ∀ᵐ ω ∂P, active i ω → active j ω → τ i ω ≠ τ j ω) :
    ∀ᵐ ω ∂P, ∀ i j : ι,
      active i ω → active j ω → τ i ω = τ j ω → i = j := by sorry
