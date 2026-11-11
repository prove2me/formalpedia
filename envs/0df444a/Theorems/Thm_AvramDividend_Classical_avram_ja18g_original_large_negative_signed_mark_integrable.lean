-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
-- name    : AvramDividend.Classical.avram_ja18g_original_large_negative_signed_mark_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:50:05.866649+00:00
-- url     : https://prove2.me/theorems/0e758fb9-5651-4c1f-b116-d93c096121a4
-- title:
--   Original large-negative Lévy marks are signed integrable under Standing
-- statement:
--   Use the Proved first-moment bound 887ac2d6 to show the identity function on the original negative-large-mark band is real Bochner-integrable against the original Lévy measure. This supports the original mean drift and signed Campbell formulae.
-- source:
--   J-A18 original zero-cutoff triplet means

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_large_negative_signed_mark_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    IntegrableOn (fun z : ℝ => z) (Iic (-1 : ℝ)) X.ν := by sorry
