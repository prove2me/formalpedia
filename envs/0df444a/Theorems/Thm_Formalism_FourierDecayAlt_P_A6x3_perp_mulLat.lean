-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_mulLat
-- name    : Formalism.FourierDecayAlt.P.A6x3.perp_mulLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:18.898247+00:00
-- url     : https://prove2.me/theorems/1546da0d-d4f7-43be-84dd-7804414ac84d
-- title:
--   A6x3: perp mul Lat
-- statement:
--   The A6x3 construction uses the perp mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L117-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L117-L128

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
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x3.perp_mulLat (b : Kˣ) (L : AddSubgroup K) :
    perp ψ (mulLat (b : K) L) = mulLat ((b⁻¹ : Kˣ) : K) (perp ψ L) := by sorry
