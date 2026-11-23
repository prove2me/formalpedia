-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G3_aux
-- name    : Formalism.FourierDecayAlt.P.G3.aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:24.288867+00:00
-- url     : https://prove2.me/theorems/c2616886-07e3-4bcf-9a64-4157782e56ec
-- title:
--   G3: aux
-- statement:
--   The G3 construction uses the aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L128-L133

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3

theorem Formalism.FourierDecayAlt.P.G3.aux (a R : ℝ) (ha : 0 ≤ a) (h : a ≤ R) : a ≤ max 1 R * min 1 a := by sorry
