-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_mulLat
-- name    : Formalism.FourierDecayAlt.P.A6x3.mem_mulLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:15.908843+00:00
-- url     : https://prove2.me/theorems/097c2d16-e150-4745-bb6a-850a77631809
-- title:
--   A6x3: mem mul Lat
-- statement:
--   The A6x3 construction uses the mem mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L104-L109

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

theorem Formalism.FourierDecayAlt.P.A6x3.mem_mulLat (b : Kˣ) {L : AddSubgroup K} {x : K} :
    x ∈ mulLat (b : K) L ↔ ((b⁻¹ : Kˣ) : K) * x ∈ L := by sorry
