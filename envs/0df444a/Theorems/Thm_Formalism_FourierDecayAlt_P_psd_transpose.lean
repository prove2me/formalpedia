-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_psd_transpose
-- name    : Formalism.FourierDecayAlt.P.psd_transpose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:05.117554+00:00
-- url     : https://prove2.me/theorems/888e1ce9-6120-4688-bbfd-f1f93f90a856
-- title:
--   P: psd transpose
-- statement:
--   The P construction uses the psd transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L469-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L469-L469

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.psd_transpose : Formalism.FourierDecayAlt.J.PSDTranspose := by sorry
