-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_ta_to_tb
-- name    : Formalism.FourierDecayAlt.P.Jx1.ta_to_tb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:01.925803+00:00
-- url     : https://prove2.me/theorems/eec85038-eb58-4daf-a2f4-fb8d97fa3d0c
-- title:
--   Jx1: ta to tb
-- statement:
--   The Jx1 construction uses the ta to tb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L265-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L265-L266

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.Jx1.ta_to_tb (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) : TB.PSDOn F k := by sorry
