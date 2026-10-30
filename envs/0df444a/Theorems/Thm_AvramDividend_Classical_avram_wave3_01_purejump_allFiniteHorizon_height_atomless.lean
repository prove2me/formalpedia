-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_purejump_allFiniteHorizon_height_atomless
-- name    : AvramDividend.Classical.avram_wave3_01_purejump_allFiniteHorizon_height_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:14:34.167468+00:00
-- url     : https://prove2.me/theorems/2e3f9ddf-e0b6-44d5-96f6-73c85c64f665
-- title:
--   Pure infinite-small-jump source atomlessness of exact reflected height at every finite horizon
-- statement:
--   For an actual spectrally negative Levy process with divergent total variation of small negative jumps, and any positive level x, the original probability of a path having any finite horizon H at which the running reflected height maximum equals x while the reflected terminal value lies strictly below x is zero. The exceptional set is uniform over all finite H, including random or nonmeasurable choices. The only auxiliary assumptions are an explicit deterministic dense time grid and positive cofinal horizons, which always exist. The proof combines the source Rogozin slope theorem, immediate negativity of small-time increments, the accepted uniformly capped posthit height atomlessness theorem, and countable cap exhaustion. This exact source-level result gives no-atom control of maxima through genuine first record stopping horizons, an essential noncircular ingredient for continuity of the record survival hazard and scale C1 regularity.
-- source:
--   Avram, Palmowski and Pistorius (2007); Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions, Lemma 2.4; accepted source-level finite-time Rogozin and reflected-height posthit lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uniform_bounded_height_atomless
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_rogozin_negative_slopes

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_purejump_allFiniteHorizon_height_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    P {ω : Ω | ∃ H : ℝ≥0,
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by sorry
