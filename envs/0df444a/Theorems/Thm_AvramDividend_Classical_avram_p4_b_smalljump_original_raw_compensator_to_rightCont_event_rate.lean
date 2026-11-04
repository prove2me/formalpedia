-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:16:00.3302+00:00
-- url     : https://prove2.me/theorems/cc36d5e2-aee9-427b-a841-ae6295db9e36
-- title:
--   Original Lévy raw predictable marked-jump compensator extends to right-continuous events
-- statement:
--   For the actual original spectrally negative Lévy jump count, the raw-filtration predictable rectangle rate for finite mark intensity extends to an event measurable in the original right-continuation at s. A sequence of later raw times carries the event and the initial source strip has vanishing intensity. The exact source rates and raw compensator remain explicit P2-dependent hypotheses.
-- source:
--   The accepted original event inclusion and short-strip eventwise future-rate squeeze, on source X and same P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_raw_after
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_rate_of_nearby_future

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont s] A)
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
    (hRaw : ∀ (u v : ℝ≥0) (C : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] C →
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, J s t ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
