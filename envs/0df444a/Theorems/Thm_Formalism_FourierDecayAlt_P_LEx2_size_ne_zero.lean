-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_size_ne_zero
-- name    : Formalism.FourierDecayAlt.P.LEx2.size_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:34.457872+00:00
-- url     : https://prove2.me/theorems/b61b6fc3-d3cb-4082-97f9-9b3cf3d30ea4
-- title:
--   LEx2: size ne zero
-- statement:
--   The LEx2 construction uses the size ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L61-L74

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

theorem Formalism.FourierDecayAlt.P.LEx2.size_ne_zero (S : Sys) (hR : S.RootsOut) (w : List (Bool × ℝ)) (hA : S.admitted w) : S.size w ≠ 0 := by sorry
