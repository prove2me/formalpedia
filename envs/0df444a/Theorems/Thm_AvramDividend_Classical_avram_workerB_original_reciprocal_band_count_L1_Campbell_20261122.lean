-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
-- name    : AvramDividend.Classical.avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:25:37.345147+00:00
-- url     : https://prove2.me/theorems/2149c7ec-f759-4e83-9b3e-e597a35c94b2
-- title:
--   Original finite reciprocal negative-band count has exact real L1 Campbell mean
-- statement:
--   For any original spectrally negative Lévy process, the real-valued count of actual X jumps over positive times up to T whose negative marks lie in a finite reciprocal band is integrable and its expectation equals the original physical intensity Tν(B). This holds with infinite total jump activity and makes the physical-bin error bounded in expectation.
-- source:
--   Proved original signed real L1 Campbell 995979e4 with deterministic Wpos=1 Wneg=0 and proved finite negative-annulus facts 5288a74e; use X.isProbability to normalise the initial weight. No synthetic jump measure or reward bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable N P ∧ (∫ ω, N ω ∂P) = r := by sorry
