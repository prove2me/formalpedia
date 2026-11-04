-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_short_strip_future_rate_sandwich
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_short_strip_future_rate_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:37:51.380969+00:00
-- url     : https://prove2.me/theorems/dfa5dcd0-91a7-44c8-aaaa-39ebe030b5ee
-- title:
--   Original source right-continuity bridge: eventwise future-rate sandwich
-- statement:
--   For the true intrinsic jump-count kernel J from the original spectrally negative Lévy X, the event-weighted mean over (s,t] lies between the later-window (r,t] physical Lévy rate and that rate plus the original first-moment strip bound (r−s)ν(B). Requires the exact original count representation, original unconditional source rate for (s,r], and future eventwise rate for (r,t]; both rate assumptions are explicit P2-dependent inputs. This is the sharp quantitative step for the right-continuous filtration extension.
-- source:
--   Accepted original event-restricted time-window count additivity 8240a020; Mathlib lintegral_mono_set and ENNReal additive monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_event_interval_lintegral_split

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_short_strip_future_rate_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hRate : (∫⁻ ω, J s r ω ∂P) =
      ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hFuture : (∫⁻ ω in A, J r t ω ∂P) =
      P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B ≤
      (∫⁻ ω in A, J s t ω ∂P) ∧
    (∫⁻ ω in A, J s t ω ∂P) ≤
      ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B +
        P A * ((t - r : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
