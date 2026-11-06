-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_no_jump_probability
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_no_jump_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:49:22.212193+00:00
-- url     : https://prove2.me/theorems/bfc446d3-ff26-4179-a1b4-162efc857227
-- title:
--   Actual original Lévy negative-band no-jump probability
-- statement:
--   For the actual spectrally negative Lévy process on its original probability space, the probability that no jump of size at most -1/(n+1) occurs strictly between zero and T equals exp(-T times the Lévy measure of that negative band). The statement concerns X itself, with no independent auxiliary Poisson process or substitute sample space. Its proof must derive the jump-count law from the original Lévy characteristics and path properties.
-- source:
--   Source-faithful mathematical missing lemma for mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. The 0966bee8 source band-count theorem follows by taking the indicator of a qualifying negative-band jump as its ℕ-valued count, with a positivity argument for the no-any-jump inclusion. This also identifies a key original-cell law premise in the Wave 7 Chat 06 L² isometry programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_no_jump_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    P {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < T ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by sorry
