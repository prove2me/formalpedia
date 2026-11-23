-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_charOf_eq_iff
-- name    : Formalism.FourierDecayAlt.P.A6x3.charOf_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:31.150812+00:00
-- url     : https://prove2.me/theorems/3b051d1f-7618-43fa-9e1b-900320f9aa3b
-- title:
--   A6x3: char Of eq iff
-- statement:
--   The A6x3 construction uses the char Of eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L155-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L155-L170

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

theorem Formalism.FourierDecayAlt.P.A6x3.charOf_eq_iff (A : AddSubgroup K) {L : AddSubgroup K} {z z' : K} (hz : z ∈ perp ψ L)
    (hz' : z' ∈ perp ψ L) : charOf A hz = charOf A hz' ↔ z - z' ∈ perp ψ A := by sorry
