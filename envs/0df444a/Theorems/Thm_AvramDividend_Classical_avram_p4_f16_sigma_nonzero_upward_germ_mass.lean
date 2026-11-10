-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f16_sigma_nonzero_upward_germ_mass
-- name    : AvramDividend.Classical.avram_p4_f16_sigma_nonzero_upward_germ_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:08:30.249535+00:00
-- url     : https://prove2.me/theorems/74ce188b-5ae9-41e5-a849-07033d4a4fab
-- title:
--   Positive near-zero excursion probability for a spectrally negative Lévy process with nonzero Gaussian coefficient
-- statement:
--   The Gaussian component is nonzero, so the process has positive upward excursions arbitrarily close to zero with positive probability. This is the Gaussian branch of the unbounded-variation Lévy regularity theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f16_sigma_nonzero_upward_germ_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ ≠ 0) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by sorry
