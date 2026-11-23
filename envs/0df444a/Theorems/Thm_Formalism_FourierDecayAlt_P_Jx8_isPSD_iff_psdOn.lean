-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_isPSD_iff_psdOn
-- name    : Formalism.FourierDecayAlt.P.Jx8.isPSD_iff_psdOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:31.884697+00:00
-- url     : https://prove2.me/theorems/9ca1119f-4f7e-4df5-af1a-c82d94d77d00
-- title:
--   Jx8: is PSD iff psd On
-- statement:
--   The Jx8 construction uses the is PSD iff psd On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L168-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L168-L207

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx8.isPSD_iff_psdOn (F : Finset α) (k : α → α → ℂ) : A5.IsPSD F k ↔ TA.PSDOn F k := by sorry
