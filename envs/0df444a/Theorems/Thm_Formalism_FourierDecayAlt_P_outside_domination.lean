-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_outside_domination
-- name    : Formalism.FourierDecayAlt.P.outside_domination
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:48.354639+00:00
-- url     : https://prove2.me/theorems/b5379309-ec0a-47f8-a415-e097c13ef6d9
-- title:
--   P: outside domination
-- statement:
--   The P construction uses the outside domination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L486-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L486-L486

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.outside_domination : Formalism.FourierDecayAlt.J.OutsideDomination := by sorry
