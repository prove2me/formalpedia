-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_comm
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:47.973803+00:00
-- url     : https://prove2.me/theorems/20bcdad2-32a3-4137-bc49-7c81d70ea29e
-- title:
--   Lie Decomposition Local: rd V comm
-- statement:
--   The Lie Decomposition Local construction uses the rd V comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L36-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L36-L57

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

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_comm {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) :
    RdV X (RdV Y Φ) g - RdV Y (RdV X Φ) g = RdV (X * Y - Y * X) Φ g := by sorry
