-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliTwoByTwo_Hpk_zero
-- name    : Formalism.FourierDecayAlt.P.CapelliTwoByTwo.Hpk_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:47:55.937208+00:00
-- url     : https://prove2.me/theorems/ed07ea04-e952-461a-9562-ef392a2fc27b
-- title:
--   Capelli Two By Two: Hpk zero
-- statement:
--   The Capelli Two By Two construction uses the Hpk zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean#L78-L87

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
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
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo

theorem Formalism.FourierDecayAlt.P.CapelliTwoByTwo.Hpk_zero (r : ℕ) (a : Fin (2 * r + 0 + 1)) :
    Hpk 0 r a ⟨r, by omega⟩ = if a = ⟨r, by omega⟩ then -1 else 0 := by sorry
