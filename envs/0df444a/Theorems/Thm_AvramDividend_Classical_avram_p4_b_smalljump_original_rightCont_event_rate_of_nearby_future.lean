-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:04:20.887113+00:00
-- url     : https://prove2.me/theorems/607e6315-9a91-4f92-9329-b1359b182448
-- title:
--   Original Lévy right-continuous future event rate via short-strip squeeze
-- statement:
--   For the exact intrinsic count of the original spectrally negative Lévy process on the same probability space, future event-weighted source rates at times approaching s from above and true finite ν intensity imply the event-weighted rate at s. The hypothesis of the raw future intensity is explicit and must be proved by P2; the right-continuous limiting passage is proved here.
-- source:
--   Accepted original-source short-strip sandwich dfa5dcd0, ENNReal continuity of coe, Tendsto.mul_const and topological order squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_short_strip_future_rate_sandwich

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s ≤ r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤) (hMass : P A ≠ ⊤)
    (hRate : ∀ n, (∫⁻ ω, J s (r n) ω ∂P) =
      ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFuture : ∀ n, (∫⁻ ω in A, J (r n) t ω ∂P) =
      P A * ((t - r n : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, J s t ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
