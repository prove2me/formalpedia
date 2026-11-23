-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_out_sub_mem
-- name    : Formalism.FourierDecayAlt.P.A6x3.out_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:11.835699+00:00
-- url     : https://prove2.me/theorems/73ea1c9a-380b-4bc1-95b7-ffa82a478ded
-- title:
--   A6x3: out sub mem
-- statement:
--   The A6x3 construction uses the out sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L40-L48

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

theorem Formalism.FourierDecayAlt.P.A6x3.out_sub_mem {Λ' Λ : AddSubgroup K} (h : Λ' ≤ Λ) (y : K ⧸ Λ') :
    (Quotient.out (AddSubgroup.quotientEquivProdOfLE h y).1 : K) - (Quotient.out y : K) ∈ Λ := by sorry
