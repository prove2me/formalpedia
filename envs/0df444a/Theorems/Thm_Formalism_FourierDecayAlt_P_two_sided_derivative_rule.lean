-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_two_sided_derivative_rule
-- name    : Formalism.FourierDecayAlt.P.two_sided_derivative_rule
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:03.676268+00:00
-- url     : https://prove2.me/theorems/ac391516-9efc-4f6e-b194-a56770a799af
-- title:
--   P: two sided derivative rule
-- statement:
--   The P construction uses the two sided derivative rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L291-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L291-L291

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.two_sided_derivative_rule : C2.TwoSided := by sorry
