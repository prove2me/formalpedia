-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_sqrt_disc
-- name    : Formalism.FourierDecayAlt.P.Jx3.sqrt_disc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:38.110924+00:00
-- url     : https://prove2.me/theorems/c0be5b10-1af9-4311-af13-8338dc26f35c
-- title:
--   Jx3: sqrt disc
-- statement:
--   The Jx3 construction uses the sqrt disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L205-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L205-L214

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3

theorem Formalism.FourierDecayAlt.P.Jx3.sqrt_disc (hD : S6.DegreeFacts) (E : Type) [Field E] [NumberField E] [IsCMField E] :
    √((|discr E| : ℤ) : ℝ) = S6.rd E ^ S6.deg E := by sorry
