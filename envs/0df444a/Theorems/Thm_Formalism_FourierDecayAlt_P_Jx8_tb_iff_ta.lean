-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_tb_iff_ta
-- name    : Formalism.FourierDecayAlt.P.Jx8.tb_iff_ta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:41.098541+00:00
-- url     : https://prove2.me/theorems/317342b1-47d1-4014-9fb1-121d0963c5ee
-- title:
--   Jx8: tb iff ta
-- statement:
--   The Jx8 construction uses the tb iff ta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L109-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L109-L138

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

theorem Formalism.FourierDecayAlt.P.Jx8.tb_iff_ta (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ TA.PSDOn F k := by sorry
