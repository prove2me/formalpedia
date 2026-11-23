-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_injective
-- name    : Formalism.FourierDecayAlt.P.A6x3.dualMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:42.385434+00:00
-- url     : https://prove2.me/theorems/061cad05-df67-4a5d-9856-f84a350eba68
-- title:
--   A6x3: dual Map injective
-- statement:
--   The A6x3 construction uses the dual Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L175-L183

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

theorem Formalism.FourierDecayAlt.P.A6x3.dualMap_injective {A : AddSubgroup K} (hA : perp ψ A = A) (L : AddSubgroup K) :
    Function.Injective (dualMap ψ A L) := by sorry
