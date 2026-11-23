-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_compactOpenChoice
-- name    : Formalism.FourierDecayAlt.P.compactOpenChoice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:17.383368+00:00
-- url     : https://prove2.me/theorems/1e9bcd38-0a2a-429d-bd94-d321fbd47f12
-- title:
--   P: compact Open Choice
-- statement:
--   The P construction uses the compact Open Choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L532-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L532-L571

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x4

theorem Formalism.FourierDecayAlt.P.compactOpenChoice : Formalism.FourierDecayAlt.A6.LatChoice := by sorry
