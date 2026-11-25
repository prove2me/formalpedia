-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_out_of_inWb
-- name    : Formalism.FourierDecayAlt.P.CapelliCoordinates.out_of_inWb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:40.184508+00:00
-- url     : https://prove2.me/theorems/8f17a125-efc5-4fd4-8211-aa2ab17b60e6
-- title:
--   Capelli Coordinates: out of in Wb
-- statement:
--   The Capelli Coordinates construction uses the out of in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L377-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliCoordinates.lean#L377-L378

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.CapelliCoordinates.out_of_inWb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : v p = 0 := by sorry
