-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_splitPrimeToDifferent
-- name    : Formalism.FourierDecayAlt.P.splitPrimeToDifferent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:55.753081+00:00
-- url     : https://prove2.me/theorems/32a473e3-8eb9-47e3-acb1-a73700dc6da0
-- title:
--   P: split Prime To Different
-- statement:
--   The P construction uses the split Prime To Different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L110-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L110-L138

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x4
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.splitPrimeToDifferent : Formalism.FourierDecayAlt.S6.SplitCoprime := by sorry
