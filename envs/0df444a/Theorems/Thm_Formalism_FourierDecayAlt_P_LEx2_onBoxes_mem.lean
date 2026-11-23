-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_onBoxes_mem
-- name    : Formalism.FourierDecayAlt.P.LEx2.onBoxes_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:24.969365+00:00
-- url     : https://prove2.me/theorems/cda4b3f6-94eb-4185-a037-714dc4ace7e2
-- title:
--   LEx2: on Boxes mem
-- statement:
--   The LEx2 construction uses the on Boxes mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L184-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L184-L193

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

theorem Formalism.FourierDecayAlt.P.LEx2.onBoxes_mem (S : Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ y ∈ w, ∃ a, a < w.length ∧ y ∈ S.box a := by sorry
