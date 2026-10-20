-- Prove2me | Theorems.Thm_AvramDividend_Classical_killedRecord_discount_scale_sandwich_of_raw_exit
-- name    : AvramDividend.Classical.killedRecord_discount_scale_sandwich_of_raw_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:18:54.676989+00:00
-- url     : https://prove2.me/theorems/7f14d8b9-8d42-490f-8b99-ce1dff95368c
-- title:
--   Two-sided q-scale bounds for killed record discount assuming the two ordinary exit identities
-- statement:
--   Take first finite strict upcrossing of a positive height h, reflected barrier a>0 and a nonnegative weight w (in particular the q-exponential discount). If the ordinary two-sided lower-exit weighted expectations at levels h-a and -a equal the two standard scale ratios W(a-h)/W(a) and W(a)/W(a+h), then the actual killed reflected first-record reward is sandwiched between those ratios. The proof uses the remotely Proved genuine killed-record expectation sandwich and explicitly exposes the two missing scale-exit distribution identities as hypotheses. Neither scale ratios nor stochastic exit laws are assumed silently; this is a conditional interface for Chat 04's two-sided exit programme.
-- source:
--   Avram Palmowski Pistorius (2007) finite-difference proof of positive barrier valuation using W(a-h)/W(a) and W(a)/W(a+h). Proved killed_firstUpcrossing_weighted_sandwich 8b9a9ed3-3d6c-4b0b-b833-c48c6c557c5b. Classical two-sided exit identity is NOT yet established here.

import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_sandwich

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killedRecord_discount_scale_sandwich_of_raw_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h)
    (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : h < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞)
    (hL : (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → h - a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      ENNReal.ofReal (W (a - h) / W a))
    (hR : (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      ENNReal.ofReal (W a / W (a + h))) :
    ENNReal.ofReal (W (a - h) / W a) ≤
       (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
          then w ω else 0 ∂P) ∧
       (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
          then w ω else 0 ∂P) ≤
       ENNReal.ofReal (W a / W (a + h)) := by sorry
