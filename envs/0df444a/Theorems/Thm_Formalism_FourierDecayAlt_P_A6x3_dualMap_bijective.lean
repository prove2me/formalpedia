-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_bijective
-- name    : Formalism.FourierDecayAlt.P.A6x3.dualMap_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:24.506891+00:00
-- url     : https://prove2.me/theorems/232767ce-7cdd-4a67-a9d9-597aa05921ef
-- title:
--   A6x3: dual Map bijective
-- statement:
--   The A6x3 construction uses the dual Map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L240-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L240-L245

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

theorem Formalism.FourierDecayAlt.P.A6x3.dualMap_bijective {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    Function.Bijective (dualMap ψ A L) := by sorry
