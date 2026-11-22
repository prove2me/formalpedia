-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_rd_pos
-- name    : Formalism.FourierDecayAlt.P.Jx3.rd_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:52.331008+00:00
-- url     : https://prove2.me/theorems/48bac43f-4eb0-463e-a1f4-ded072b49e92
-- title:
--   Jx3: rd pos
-- statement:
--   The Jx3 construction uses the rd pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L178-L182

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

theorem Formalism.FourierDecayAlt.P.Jx3.rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by sorry
