-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_MajIsProf
-- name    : Formalism.FourierDecayAlt.P.Jx2.t_MajIsProf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:45.332733+00:00
-- url     : https://prove2.me/theorems/55f03718-173a-4431-ace5-759121b5a7cd
-- title:
--   Jx2: t Maj Is Prof
-- statement:
--   The Jx2 construction uses the t Maj Is Prof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L9-L13

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate

theorem Formalism.FourierDecayAlt.P.Jx2.t_MajIsProf : MajIsProf := by sorry
