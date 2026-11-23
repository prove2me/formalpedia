-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_on_iff
-- name    : Formalism.FourierDecayAlt.P.LEx2.on_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:37.93531+00:00
-- url     : https://prove2.me/theorems/a5b6d617-66f6-4884-ba02-d6e995fcccd2
-- title:
--   LEx2: on iff
-- statement:
--   The LEx2 construction uses the on iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L153-L158

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

theorem Formalism.FourierDecayAlt.P.LEx2.on_iff (S : Sys) (N : ℕ) (Y : Fin N → ℝ) : (S.fam N).On Y ↔ S.OnBoxes (List.ofFn Y) := by sorry
