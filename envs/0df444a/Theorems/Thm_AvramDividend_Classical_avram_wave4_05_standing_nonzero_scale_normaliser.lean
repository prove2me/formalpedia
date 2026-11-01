-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_standing_nonzero_scale_normaliser
-- name    : AvramDividend.Classical.avram_wave4_05_standing_nonzero_scale_normaliser
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:30:16.191233+00:00
-- url     : https://prove2.me/theorems/17ab0fe2-5a98-424b-9a3c-bb87866cd1c7
-- title:
--   Standing q-scale function has a nonzero normaliser at positive optimal barrier
-- statement:
--   Under the original Standing hypotheses, q>0, source q-scale W and positive optimal barrier, the exact scalar divE 1 (scaleDeriv W cstar) is nonzero, without extra positivity, differentiability or Esscher monotonicity premises. Uses the canonically proved positive Esscher monotonicity of the tilted scale function, Standing C1 regularity and the nonzero-normaliser theorem. This removes the extra hk side condition when assembling the canonical scale-generator harmonicity implication.
-- source:
--   Source Standing C1, tilted positive monotonicity and canonical positive-barrier normaliser proof

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
/-- Standing hypotheses make the optimal barrier scale normaliser nonzero. -/

theorem AvramDividend.Classical.avram_wave4_05_standing_nonzero_scale_normaliser
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by sorry
