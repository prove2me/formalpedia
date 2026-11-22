-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_SizesToRecursion
-- name    : Formalism.FourierDecayAlt.P.Jx7.t_SizesToRecursion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:13.190111+00:00
-- url     : https://prove2.me/theorems/b188fd01-370d-4676-b346-fe19370ac157
-- title:
--   Jx7: t Sizes To Recursion
-- statement:
--   The Jx7 construction uses the t Sizes To Recursion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L499-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L499-L540

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
open scoped ComplexOrder

theorem Formalism.FourierDecayAlt.P.Jx7.t_SizesToRecursion : SizesToRecursion := by sorry
