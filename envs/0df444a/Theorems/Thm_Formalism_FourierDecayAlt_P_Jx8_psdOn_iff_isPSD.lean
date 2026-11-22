-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psdOn_iff_isPSD
-- name    : Formalism.FourierDecayAlt.P.Jx8.psdOn_iff_isPSD
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:21.811804+00:00
-- url     : https://prove2.me/theorems/86c3531a-fe83-46e6-901f-a56d5f55e476
-- title:
--   Jx8: psd On iff is PSD
-- statement:
--   The Jx8 construction uses the psd On iff is PSD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L213-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L213-L214

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

theorem Formalism.FourierDecayAlt.P.Jx8.psdOn_iff_isPSD (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ A5.IsPSD F k := by sorry
