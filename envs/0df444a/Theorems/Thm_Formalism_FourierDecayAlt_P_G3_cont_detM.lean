-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G3_cont_detM
-- name    : Formalism.FourierDecayAlt.P.G3.cont_detM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.763395+00:00
-- url     : https://prove2.me/theorems/a43a9ae3-a42c-4547-a112-f5d183957b46
-- title:
--   G3: cont det M
-- statement:
--   The G3 construction uses the cont det M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean#L124-L126

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

theorem Formalism.FourierDecayAlt.P.G3.cont_detM (s : ℕ) : Continuous (detM : Mat s → ℂ) := by sorry
