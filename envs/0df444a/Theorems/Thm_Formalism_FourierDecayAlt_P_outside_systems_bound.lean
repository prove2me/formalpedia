-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_outside_systems_bound
-- name    : Formalism.FourierDecayAlt.P.outside_systems_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:44.153581+00:00
-- url     : https://prove2.me/theorems/40fe2df7-5171-4f81-b143-58488a15e6a9
-- title:
--   P: outside systems bound
-- statement:
--   The P construction uses the outside systems bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L484-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L484-L484

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

theorem Formalism.FourierDecayAlt.P.outside_systems_bound : Formalism.FourierDecayAlt.J.OutsideSysOk := by sorry
