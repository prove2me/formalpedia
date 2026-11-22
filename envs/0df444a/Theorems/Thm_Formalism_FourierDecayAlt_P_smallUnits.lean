-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_smallUnits
-- name    : Formalism.FourierDecayAlt.P.smallUnits
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:21.608911+00:00
-- url     : https://prove2.me/theorems/a141725b-641b-4c28-92ee-2dec5c4aba84
-- title:
--   P: small Units
-- statement:
--   The P construction uses the small Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L523-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L523-L530

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

theorem Formalism.FourierDecayAlt.P.smallUnits : Formalism.FourierDecayAlt.A6.SmallUnits := by sorry
