-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_dOpLin_of
-- name    : Formalism.FourierDecayAlt.P.qr_dOpLin_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:32.44181+00:00
-- url     : https://prove2.me/theorems/bb97c635-2852-46b0-b5ed-95659b841e4d
-- title:
--   P: qr d Op Lin of
-- statement:
--   The P construction uses the qr d Op Lin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L204-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean#L204-L216

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.qr_dOpLin_of (hT : Formalism.FourierDecayAlt.Qr.Trotter) (hM : Formalism.FourierDecayAlt.Qr.TrotterMx) (hP : Formalism.FourierDecayAlt.Qr.PiExp) :
    Formalism.FourierDecayAlt.Qr.DOpLin := by sorry
