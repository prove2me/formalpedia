-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_Sup_lie
-- name    : Formalism.FourierDecayAlt.P.CapelliCoordinates.Sup.lie
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:42.295796+00:00
-- url     : https://prove2.me/theorems/5c2ff4cb-0587-4610-82da-46264e218c9b
-- title:
--   Sup: lie
-- statement:
--   The Sup construction uses the lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L146-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L146-L180

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.CapelliCoordinates.Sup.lie {Z : Mx k r} (hZ : Sup k r i Z) :
    inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z) := by sorry
