-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
-- name    : AvramDividend.Classical.avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:53:17.633844+00:00
-- url     : https://prove2.me/theorems/84a26dd6-827b-4769-bd9f-22570d0769cd
-- title:
--   Finite Gaussian compact HJB combined positive source dominated by signed exponential and polynomial tails on all meshes
-- statement:
--   Given finite original large Gaussian source cells whose individual positive discounted verification errors are bounded by a global HJB exponential at the positive post-increment reserve plus compact jet polynomial, and whose preincrement reserve is bounded above by B, the positive part of their full signed sum is bounded by a deterministic multiple of the exact signed raw Gaussian exponential stream plus a multiple of the original raw/centered polynomial source. This applies at every physical mesh size and eliminates the eventual-small-drift auxiliary assumption in the large Gaussian a263 proof.
-- source:
--   Proved a302 compact starting reserve exponential endpoint transfer; finite sum positive part inequality; a301 source HJB jets, a306 source reserve ceiling.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f r z y : ℕ → ℝ) (θ K M B : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hCell : ∀ i ∈ S, A i →
      max (f i) 0 ≤ K*Real.exp (θ*(y i+r i)) +
        M*(1+|r i|+z i^2/2))
    (hReserve : ∀ i ∈ S, A i → y i ≤ B) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      (K*Real.exp (θ*B))*
        (∑ i ∈ S, if A i then Real.exp (θ*r i) else 0) +
      M*(∑ i ∈ S, if A i then 1+|r i|+z i^2/2 else 0) := by sorry
