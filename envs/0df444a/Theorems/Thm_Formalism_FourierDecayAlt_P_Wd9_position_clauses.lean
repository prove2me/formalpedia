-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_position_clauses
-- name    : Formalism.FourierDecayAlt.P.Wd9.position_clauses
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:41.407805+00:00
-- url     : https://prove2.me/theorems/e92ae6fb-9f10-4542-9c7e-8db6dd42cfd2
-- title:
--   Wd9: position clauses
-- statement:
--   The Wd9 construction uses the position clauses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L170-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L170-L188

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

theorem Formalism.FourierDecayAlt.P.Wd9.position_clauses (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K)
    (hF : ∀ Y, FreeOf2 a (TT Y)) (hdet : DetAt TT q Y) (hq : q Y ≠ 0) :
    ins a (TT Y) * PsiP TT q a Y = ins a JJᵀ ∧
    PsiP TT q a Y * ins a (JJ * TT Y) = 1 ∧
    ins a (JJ * TT Y) * PsiP TT q a Y = 1 := by sorry
