-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_adjComm_of_parts
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjComm_of_parts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:12.286785+00:00
-- url     : https://prove2.me/theorems/80351fcb-b181-443e-affc-25c40099a410
-- title:
--   FFS: adj Comm of parts
-- statement:
--   The FFS construction uses the adj Comm of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAdjCut.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAdjCut.lean#L38-L41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjCut
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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjComm_of_parts (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by sorry
