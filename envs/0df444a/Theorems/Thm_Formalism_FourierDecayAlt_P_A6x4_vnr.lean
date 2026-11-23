-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_vnr
-- name    : Formalism.FourierDecayAlt.P.A6x4.vnr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:37.14182+00:00
-- url     : https://prove2.me/theorems/953a5549-4a96-4ef1-b32b-38660a74d87f
-- title:
--   A6x4: vnr
-- statement:
--   The A6x4 construction uses the vnr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L93-L104

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
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.A6x4.vnr [IsArtinianRing K] [IsReduced K] (z : K) : ∃ c, z = z * z * c := by sorry
