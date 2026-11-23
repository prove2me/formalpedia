-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_mulLat
-- name    : Formalism.FourierDecayAlt.P.A6x3.volL_mulLat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:50.28949+00:00
-- url     : https://prove2.me/theorems/dda7c595-99d5-4170-8f4c-29441cba1715
-- title:
--   A6x3: vol L mul Lat
-- statement:
--   The A6x3 construction uses the vol L mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L81-L86

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.A6x3.volL_mulLat {R : Subring K} (hR : Lat R.toAddSubgroup) (b : Kˣ) {L : AddSubgroup K}
    (hL : Lat L) : volL R (mulLat (b : K) L) = modK R (b : K) * volL R L := by sorry
