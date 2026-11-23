-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_onBoxes_ofFn
-- name    : Formalism.FourierDecayAlt.P.LEx2.onBoxes_ofFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:47.386608+00:00
-- url     : https://prove2.me/theorems/c8b739d4-936f-4188-9c2b-27b131b2bef6
-- title:
--   LEx2: on Boxes of Fn
-- statement:
--   The LEx2 construction uses the on Boxes of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L128-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L128-L151

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

theorem Formalism.FourierDecayAlt.P.LEx2.onBoxes_ofFn (S : Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) ↔ ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by sorry
