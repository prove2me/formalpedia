-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_core
-- name    : Formalism.FourierDecayAlt.P.Fr5.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:02.966844+00:00
-- url     : https://prove2.me/theorems/69ebfb65-3549-44b2-80a5-3067244d39d4
-- title:
--   Fr5: core
-- statement:
--   The Fr5 construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L19-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L19-L66

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Fr5.core (F Fi d τ τi τ' τi' l RR T00 T01 T10 T11 U10 U11 : B) (q : ℂ)
    (hRR : RR = star F * d * F) (hF : F * Fi = 1) (hF' : Fi * F = 1)
    (hdτ : star (d * τ) = d * τ) (hτ : τi * τ = 1) (hτ1 : τ' * τi' = 1) (hτ2 : τi' * τ' = 1)
    (h11 : F * T11 = τ * F) (h10 : F * T10 = τ * l * F) (hU : F * U11 = τ' * F)
    (herm : star (RR * T10) = RR * T01)
    (quantum_determinant_shifted : T00 * U11 - T01 * U10 = q • (1 : B)) (upper_block_det_one : T10 * U11 = T11 * U10) :
    RR * T11 = star F * (d * τ) * F ∧ RR * T10 = star F * (d * τ * l) * F ∧
      RR * T01 = star F * (star l * (d * τ)) * F ∧
      RR * T00 = star F * (q • (d * τi') + star l * (d * τ) * l) * F := by sorry
