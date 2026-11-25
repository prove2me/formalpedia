-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_jAFFStable_of_parts
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.jAFFStable_of_parts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:46.169076+00:00
-- url     : https://prove2.me/theorems/95553727-811c-4f54-9f88-090319c8a483
-- title:
--   FFS: j AFFStable of parts
-- statement:
--   The FFS construction uses the j AFFStable of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAsm.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAsm.lean#L12-L35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.JA.FFS.jAFFStable_of_parts (hG : GermOps) (hE : ExtLoc) (hS : SmoothOps) (hA : AdjComm) (hQ : EquivOps)
    (hO : OmPDom) : JAFFStable := by sorry
