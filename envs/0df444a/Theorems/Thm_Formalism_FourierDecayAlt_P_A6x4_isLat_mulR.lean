-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_isLat_mulR
-- name    : Formalism.FourierDecayAlt.P.A6x4.isLat_mulR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:35.827542+00:00
-- url     : https://prove2.me/theorems/5d178eeb-3148-4c91-9114-96e2c5a485f9
-- title:
--   A6x4: is Lat mul R
-- statement:
--   The A6x4 construction uses the is Lat mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L117-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L117-L129

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x4.isLat_mulR (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) : IsLat (mulR R a) := by sorry
