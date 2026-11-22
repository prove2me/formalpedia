-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_doubleMeanSplit
-- name    : Formalism.FourierDecayAlt.P.doubleMeanSplit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:39.211236+00:00
-- url     : https://prove2.me/theorems/d22afa9e-6444-48a0-8cd6-4419d6e79f67
-- title:
--   P: double Mean Split
-- statement:
--   The P construction uses the double Mean Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L25-L34

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by sorry
