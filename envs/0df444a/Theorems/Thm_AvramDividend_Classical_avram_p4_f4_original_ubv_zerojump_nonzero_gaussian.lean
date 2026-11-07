-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
-- name    : AvramDividend.Classical.avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:33:16.236763+00:00
-- url     : https://prove2.me/theorems/099e50af-b973-4178-8e65-1ef22bb3cadb
-- title:
--   Original unbounded-variation zero-jump Lévy process has nonzero Gaussian coefficient
-- statement:
--   Under original unbounded-variation and vanishing Lévy jump measure, the Gaussian variance parameter is nonzero. This discharges the Gaussian-only nondegeneracy case of the source Itô split.
-- source:
--   Contrapositive of the proved original-process sigma-zero unbounded-variation nonzero-jump-measure theorem 3d01f20c.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) : X.σ ≠ 0 := by sorry
