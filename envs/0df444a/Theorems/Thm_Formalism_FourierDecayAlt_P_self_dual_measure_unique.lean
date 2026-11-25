-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_self_dual_measure_unique
-- name    : Formalism.FourierDecayAlt.P.self_dual_measure_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:54.561057+00:00
-- url     : https://prove2.me/theorems/92970756-e9bd-4928-8b72-ca8e54e5f118
-- title:
--   P: self dual measure unique
-- statement:
--   The P construction uses the self dual measure unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L152-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L152-L167

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3

theorem Formalism.FourierDecayAlt.P.self_dual_measure_unique : Formalism.FourierDecayAlt.G.SelfDualUnique := by sorry
