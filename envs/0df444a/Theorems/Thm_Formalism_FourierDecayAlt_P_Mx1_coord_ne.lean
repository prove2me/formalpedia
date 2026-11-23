-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_coord_ne
-- name    : Formalism.FourierDecayAlt.P.Mx1.coord_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:57.540223+00:00
-- url     : https://prove2.me/theorems/4293588e-dbc5-4905-9c60-ac309de406ab
-- title:
--   Mx1: coord ne
-- statement:
--   The Mx1 construction uses the coord ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L7-L8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx1

theorem Formalism.FourierDecayAlt.P.Mx1.coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by sorry
