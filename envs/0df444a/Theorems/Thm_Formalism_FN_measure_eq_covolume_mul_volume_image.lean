-- Prove2me | Theorems.Thm_Formalism_FN_measure_eq_covolume_mul_volume_image
-- name    : Formalism.FN.measure_eq_covolume_mul_volume_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:20.115079+00:00
-- url     : https://prove2.me/theorems/5f8f65b2-745a-4130-bbc7-697527c271c2
-- title:
--   FN: measure eq covolume mul volume image
-- statement:
--   The FN construction uses the measure eq covolume mul volume image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MeasureEqCovolumeMulVolumeImage.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MeasureEqCovolumeMulVolumeImage.lean#L10-L44

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN

theorem Formalism.FN.measure_eq_covolume_mul_volume_image {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type} [Fintype ι] (b : Basis ι ℤ L) (S : Set E) :
    μ S = ENNReal.ofReal (ZLattice.covolume L μ) *
      volume ((b.ofZLatticeBasis ℝ L).equivFun '' S) := by sorry
