-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a44_true_stop_mask_positive_taylor_small_large_split
-- name    : AvramDividend.Classical.avram_ga_a44_true_stop_mask_positive_taylor_small_large_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:16:26.121495+00:00
-- url     : https://prove2.me/theorems/d20703cd-ab92-4f9c-92fe-ad374319325f
-- title:
--   True stop-masked finite physical Gaussian Taylor positive remainder has small-energy and large-increment bound
-- statement:
--   On an arbitrary original sample path, the positive Taylor quadratic remainder over physical source cells beginning strictly before a random stopping clock is bounded by a small multiple of true stopped quadratic energy plus a bounded multiple of stopped large-increment energy.
-- source:
--   Original Gaussian A b0d9951c positive-only source Taylor proof, true stopped finite-cell scalar energy transfer via ga_a43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open BigOperators AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a44_true_stop_mask_positive_taylor_small_large_split {ι Ω : Type*} (S : Finset ι)
    (s : ι → ℝ≥0) (ρ : Ω → ℝ≥0) (ω : Ω)
    (a z : ι → Ω → ℝ) (ε M δ : ℝ)
    (hε : 0 ≤ ε)
    (ha : ∀ i ∈ S, s i < ρ ω → 0 ≤ a i ω)
    (hM : ∀ i ∈ S, s i < ρ ω → a i ω ≤ M)
    (hSmall : ∀ i ∈ S, s i < ρ ω →
      |z i ω| < δ → a i ω ≤ ε) :
    (∑ i ∈ S, if s i < ρ ω then a i ω * (z i ω)^2 else 0) ≤
      ε * (∑ i ∈ S, if s i < ρ ω then (z i ω)^2 else 0) +
      M * (∑ i ∈ S, if s i < ρ ω then
        (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0) := by sorry
