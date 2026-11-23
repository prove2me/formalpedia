-- Prove2me | Theorems.Thm_Formalism_FN_LowerVolumeBound_covol_le
-- name    : Formalism.FN.LowerVolumeBound.covol_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:45.6849+00:00
-- url     : https://prove2.me/theorems/182c8a88-6c57-49d0-8805-f0bc3d436418
-- title:
--   Lower Volume Bound: covol le
-- statement:
--   The Lower Volume Bound construction uses the covol le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkowskiIILowerOf.lean#L39-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkowskiIILowerOf.lean#L39-L73

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN Formalism.FN.LowerVolumeBound

theorem Formalism.FN.LowerVolumeBound.covol_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (bv : Basis (Fin (finrank ℝ E)) ℝ E) (hv : ∀ i, bv i ∈ L) :
    ZLattice.covolume L μ ≤ μ.real (parallelepiped bv) := by sorry
