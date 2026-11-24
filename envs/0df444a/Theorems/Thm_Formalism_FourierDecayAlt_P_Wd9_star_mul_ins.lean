-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_star_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Wd9.star_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:13.769271+00:00
-- url     : https://prove2.me/theorems/e60424a9-b7ff-4176-a219-7ac7357421e7
-- title:
--   Wd9: star mul ins
-- statement:
--   The Wd9 construction uses the star mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L145-L147

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))

theorem Formalism.FourierDecayAlt.P.Wd9.star_mul_ins {a : S} {RR : SlopeTestRemainingChoices S A} (hR : FreeOf a RR) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M)
    (h : (d0 RR * M)ᴴ = d0 RR * M) : star (RR * ins a M) = RR * ins a M := by sorry
