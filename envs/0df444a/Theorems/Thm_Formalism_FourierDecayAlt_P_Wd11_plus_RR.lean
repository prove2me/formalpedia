-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_plus_RR
-- name    : Formalism.FourierDecayAlt.P.Wd11.plus_RR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:36.41301+00:00
-- url     : https://prove2.me/theorems/61eaf625-3c20-49df-90c6-d22cd8f7242e
-- title:
--   Wd11: plus RR
-- statement:
--   The Wd11 construction uses the plus RR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L523-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L523-L537

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd11.plus_RR (a : S) (s : K) {V Vi RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf a V) (hVi : FreeOf a Vi) (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    star (ins a (lift0 (Uinv (A := A) s)) * V) * (RR * ins a T) *
        (ins a (lift0 (Uinv (A := A) s)) * V) = RR * ins a T := by sorry
