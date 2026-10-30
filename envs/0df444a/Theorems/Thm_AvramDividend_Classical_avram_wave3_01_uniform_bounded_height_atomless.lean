-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uniform_bounded_height_atomless
-- name    : AvramDividend.Classical.avram_wave3_01_uniform_bounded_height_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:28:27.62246+00:00
-- url     : https://prove2.me/theorems/30022d35-815b-4248-9de5-6b9bba5374f0
-- title:
--   Uniform positive-height atomlessness over all bounded random reflected horizons
-- statement:
--   Fix a finite cap N and a positive reflected-drawdown height x. For a genuine downward-regular spectrally negative Levy process, the original probability assigns zero mass to all sample paths for which there exists ANY horizon H no later than N with reflected maximum exactly x and terminal reflected value below x. This improves ordinary fixed-horizon null results to one exceptional P-null set uniform in H, allowing H to be a first upward record or any random (even nonmeasurable) horizon. The proof uses source finite-stopping posthit negative regularity at the capped first closed-level-x hit, pathwise upper-semicontinuity to attain x before H, and the reflected overshoot after the hit. It requires no Ito excursion measure or scale C1 hypothesis. As part of the pure infinite-small-jump branch, the source Rogozin slope lemma already proves hRegular from the target variation assumption. It isolates a noncircular stochastic component of continuity of record-level drawdown survival probabilities.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Levy Processes, Lemma 2.4; source Prove2Me finite-stopping post-hit regularity and reflected-height overshoot theorems.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_uniform_bounded_height_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω | ∃ H : ℝ≥0, H ≤ N ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by sorry
