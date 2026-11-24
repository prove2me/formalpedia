-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_add
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:48.962879+00:00
-- url     : https://prove2.me/theorems/78f2bcfc-ca83-4e0d-a56e-a15a00b98e7c
-- title:
--   Lie Decomposition Local: rd V add
-- statement:
--   The Lie Decomposition Local construction uses the rd V add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L59-L63

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_add {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X + Y) Φ g = RdV X Φ g + RdV Y Φ g := by sorry
