-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx4_rd_pos
-- name    : Formalism.FourierDecayAlt.P.Jx4.rd_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:42.679651+00:00
-- url     : https://prove2.me/theorems/a8503d1b-4fea-46c7-b660-bb9dfd8df652
-- title:
--   Jx4: rd pos
-- statement:
--   The Jx4 construction uses the rd pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonJointFirstReduction.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonJointFirstReduction.lean#L11-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Jx4

theorem Formalism.FourierDecayAlt.P.Jx4.rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by sorry
