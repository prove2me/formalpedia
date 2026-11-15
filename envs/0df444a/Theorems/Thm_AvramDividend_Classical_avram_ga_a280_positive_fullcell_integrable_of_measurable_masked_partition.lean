-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
-- name    : AvramDividend.Classical.avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:20:06.965404+00:00
-- url     : https://prove2.me/theorems/8fac0be9-9e30-4e77-afa6-fc621aec268b
-- title:
--   Measurable full source positive part integrable under integrable small and large masked positive parts
-- statement:
--   For an a.e. strongly measurable original full-cell source positive part, if integrable positive small-cell and large-cell sources dominate it pointwise, the original full positive source is integrable. This is the exact finite-grid integrability transfer used in the a216 original Gaussian source-exact partition, avoiding any assumption on the absolute value of the undiscounted HJB value.
-- source:
--   Mathlib Integrable.mono and original Gaussian a216 positive source partition a266

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S L : Ω → ℝ)
    (hFm : AEStronglyMeasurable (fun ω => max (F ω) 0) P)
    (hSi : Integrable (fun ω => max (S ω) 0) P)
    (hLi : Integrable (fun ω => max (L ω) 0) P)
    (hPt : ∀ ω, max (F ω) 0 ≤ max (S ω) 0+max (L ω) 0) :
    Integrable (fun ω => max (F ω) 0) P := by sorry
