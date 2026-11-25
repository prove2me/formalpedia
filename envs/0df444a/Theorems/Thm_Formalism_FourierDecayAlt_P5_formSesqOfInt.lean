-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_formSesqOfInt
-- name    : Formalism.FourierDecayAlt.P5.formSesqOfInt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:20.253097+00:00
-- url     : https://prove2.me/theorems/ce017ebb-e1f6-4c4f-86eb-657e0c736ea4
-- title:
--   P5: form Sesq Of Int
-- statement:
--   The P5 construction uses the form Sesq Of Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L112-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HsInnerAddSmulRight.lean#L112-L127

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem Formalism.FourierDecayAlt.P5.formSesqOfInt : FormSesqOfInt := by sorry
