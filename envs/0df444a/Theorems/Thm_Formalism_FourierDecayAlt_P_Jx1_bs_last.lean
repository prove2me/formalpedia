-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_bs_last
-- name    : Formalism.FourierDecayAlt.P.Jx1.bs_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:24.3628+00:00
-- url     : https://prove2.me/theorems/7745a9ba-2212-41d3-b843-eeb1cb6f1829
-- title:
--   Jx1: bs last
-- statement:
--   The Jx1 construction uses the bs last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L135-L140

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
variable {E : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.Jx1.bs_last (h : TB.Pt E) (s : ℕ) (t : E) :
    TB.blockStart (h ++ [(s, t)]) h.length = TB.level h + 1 := by sorry
