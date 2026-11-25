-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_branchingK_of
-- name    : Formalism.FourierDecayAlt.P.qr_branchingK_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:09:09.909583+00:00
-- url     : https://prove2.me/theorems/45f87d5b-034b-4b2a-86b3-7f1b3c0aa77c
-- title:
--   P: qr branching K of
-- statement:
--   The P construction uses the qr branching K of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L88-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameExtension.lean#L88-L115

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by sorry
