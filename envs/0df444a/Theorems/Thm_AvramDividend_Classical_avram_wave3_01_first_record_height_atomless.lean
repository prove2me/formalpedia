-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_first_record_height_atomless
-- name    : AvramDividend.Classical.avram_wave3_01_first_record_height_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T01:14:42.999236+00:00
-- url     : https://prove2.me/theorems/35f216f9-e40c-4f5e-9c85-c4a5979d76ce
-- title:
--   Infinite-small-jump Lévy reflected maximum before any finite first upward record has no positive fixed-height atom
-- statement:
--   Under source infinite small-jump variation and the same deterministic rational-grid hypotheses as the already Proved all-finite-horizon reflected-height theorem, for any b≥0 and x>0 the event that the maximum reflected drawdown up to a finite first upward record T_b is exactly x has probability zero. At an attained upward record the reflected drawdown is exactly zero, so this event lies in the canonically Proved null event consisting of some finite horizon H with global reflected maximum x but terminal reflected drawdown <x. This is directly relevant to continuity in the killing barrier of the genuine first-record survival expectation and hence the scale-derivative hazard.
-- source:
--   Original SNLP first-upcrossing record equals reflected drawdown zero plus accepted pure infinite-small-jump all-horizon height theorem; KKR (2013) scale C1 regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_purejump_allFiniteHorizon_height_atomless

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_first_record_height_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a c : ℝ≥0, a < c →
      ∃ m : ℕ, a < times m ∧ times m < c)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    P {ω : Ω | ∃ u : ℝ≥0,
      (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = (x : ℝ)} = 0 := by sorry
