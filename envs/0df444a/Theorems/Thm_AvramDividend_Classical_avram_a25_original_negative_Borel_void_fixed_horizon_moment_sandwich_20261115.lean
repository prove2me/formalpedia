-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:55:00.341784+00:00
-- url     : https://prove2.me/theorems/cfed11b6-729e-4ca7-bfaf-c42f677acee7
-- title:
--   Original Borel physical jump void deficit bounded by source first and second factorial moments at a fixed horizon
-- statement:
--   For the original spectrally negative Lévy process and actual finite-activity negative Borel jump measure, at every fixed horizon s, with r=sν(B), the probability of at least one B-jump satisfies r−r²/2 ≤ P(N_s(B)>0) ≤ r. Use the proved first physical count moment and exact second factorial moment, the proved natural count realisation and finite count a.e., and the generic integrated occupancy bound. This fixed-horizon source statement is the stochastic core of the small-time Poisson void slope and, through the already proved semigroup theorem, the exact Poisson void probability. All processes and measures remain original.
-- source:
--   Proved first moment 4faa7c77, second factorial 6d1258a3, natural count realisation 84a4791e, finite negative count a.e. and a25 integrated occupancy inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_void_fixed_horizon_moment_sandwich_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
    let deficit : ℝ := 1 - (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B) = 0}).toReal
    r - r ^ 2 / 2 ≤ deficit ∧ deficit ≤ r := by sorry
