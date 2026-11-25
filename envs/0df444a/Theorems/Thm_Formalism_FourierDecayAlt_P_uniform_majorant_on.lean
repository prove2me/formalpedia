-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_uniform_majorant_on
-- name    : Formalism.FourierDecayAlt.P.uniform_majorant_on
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:50.133067+00:00
-- url     : https://prove2.me/theorems/39c5c191-810f-4e15-a38d-ea6b222373aa
-- title:
--   P: uniform majorant on
-- statement:
--   The P construction uses the uniform majorant on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L490-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L490-L490

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

theorem Formalism.FourierDecayAlt.P.uniform_majorant_on : Formalism.FourierDecayAlt.J.UniformMajorantOn := by sorry
