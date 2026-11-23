-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_crossTermsVanish
-- name    : Formalism.FourierDecayAlt.P.crossTermsVanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:09.150523+00:00
-- url     : https://prove2.me/theorems/ca12a0d6-74f3-4aaf-890b-ec83d885498b
-- title:
--   P: cross Terms Vanish
-- statement:
--   The P construction uses the cross Terms Vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L904-L905
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L904-L905

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

theorem Formalism.FourierDecayAlt.P.crossTermsVanish : Formalism.FourierDecayAlt.A6.CrossVanish := by sorry
