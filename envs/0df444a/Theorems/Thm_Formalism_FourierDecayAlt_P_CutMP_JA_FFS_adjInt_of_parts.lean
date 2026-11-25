-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_adjInt_of_parts
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjInt_of_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:28:56.941719+00:00
-- url     : https://prove2.me/theorems/fcd4820e-ffc3-4e8a-8300-11f10bf009f4
-- title:
--   FFS: adj Int of parts
-- statement:
--   The FFS construction uses the adj Int of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAdjIntCut.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAdjIntCut.lean#L30-L30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjIntCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjInt_of_parts (hA : AdjIntAsm) (hU : RhoUni) (hF : FormAdj) : AdjInt := by sorry
