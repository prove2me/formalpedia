-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_l_mat
-- name    : Formalism.FourierDecayAlt.P.Fr9.l_mat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:04.699829+00:00
-- url     : https://prove2.me/theorems/695d7af0-6f81-4136-86c1-deef09c1b61c
-- title:
--   Fr9: l mat
-- statement:
--   The Fr9 construction uses the l mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L477-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L477-L483

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr9.l_mat {B : Type*} [Ring B] {E Gb τn Ln N dg Ln' lm : Matrix (Fin 2) (Fin 2) B} (m3 : τn * Ln = N)
    (m4 : Gb * τn = dg * Gb) (m5 : Gb * Ln = Ln' * Gb) (e1 : E * dg = dg * E) (e2 : E * Ln' = lm * E) :
    E * Gb * N = dg * lm * (E * Gb) := by sorry
