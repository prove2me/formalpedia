-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_conv
-- name    : Formalism.FourierDecayAlt.P.Jx1.conv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:54.179288+00:00
-- url     : https://prove2.me/theorems/647233cf-4482-4b9d-a107-9bbde87cbec6
-- title:
--   Jx1: conv
-- statement:
--   The Jx1 construction uses the conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L8-L29

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

theorem Formalism.FourierDecayAlt.P.Jx1.conv {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TB.PSDOn F k) :
    TA.PSDOn F (fun x y => k y x) := by sorry
