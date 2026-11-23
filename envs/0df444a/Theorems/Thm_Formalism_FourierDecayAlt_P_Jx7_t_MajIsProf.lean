-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_MajIsProf
-- name    : Formalism.FourierDecayAlt.P.Jx7.t_MajIsProf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:30.815806+00:00
-- url     : https://prove2.me/theorems/31e60ac7-a114-49d7-a9cd-0f708a5730f0
-- title:
--   Jx7: t Maj Is Prof
-- statement:
--   The Jx7 construction uses the t Maj Is Prof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L315-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L315-L321

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.Jx7.t_MajIsProf : MajIsProf := by sorry
