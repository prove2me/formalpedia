-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_level_append
-- name    : Formalism.FourierDecayAlt.P.Jx1.level_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:35.371884+00:00
-- url     : https://prove2.me/theorems/307504e5-e6bc-42f5-8b88-06223ea8edda
-- title:
--   Jx1: level append
-- statement:
--   The Jx1 construction uses the level append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L167-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean#L167-L168

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

theorem Formalism.FourierDecayAlt.P.Jx1.level_append (h : TB.Pt E) (s : ℕ) (t : E) : TB.level (h ++ [(s, t)]) = TB.level h + s := by sorry
