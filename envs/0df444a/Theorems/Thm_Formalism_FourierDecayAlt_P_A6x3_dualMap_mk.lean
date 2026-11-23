-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_dualMap_mk
-- name    : Formalism.FourierDecayAlt.P.A6x3.dualMap_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:17.198962+00:00
-- url     : https://prove2.me/theorems/948c7bfe-ef42-42a3-bd42-7d7d261f4868
-- title:
--   A6x3: dual Map mk
-- statement:
--   The A6x3 construction uses the dual Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L185-L191

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

theorem Formalism.FourierDecayAlt.P.A6x3.dualMap_mk {A : AddSubgroup K} (hA : perp ψ A = A) {L : AddSubgroup K} {z : K}
    (hz : z ∈ perp ψ L) :
    dualMap ψ A L ((⟨z, hz⟩ : perp ψ L) : perp ψ L ⧸ A.addSubgroupOf (perp ψ L)) = charOf A hz := by sorry
