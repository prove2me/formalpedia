-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ee_abs
-- name    : Formalism.FourierDecayAlt.P.Fr9.ee_abs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:04:01.989549+00:00
-- url     : https://prove2.me/theorems/451b5a91-f6c1-4a10-81a4-86d1f28bd05c
-- title:
--   Fr9: ee abs
-- statement:
--   The Fr9 construction uses the ee abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L422-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L422-L441

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
variable {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr9.ee_abs {B : Type*} [Ring B] {g gi k ki x xi L0 e D w : B} (hg : gi * g = 1) (hk : ki * k = 1)
    (hx : xi * x = 1) (xk : x * k = k * x) (eg : e * g = g * e) (kg : k * g = g * k) (xL : x * L0 = L0 * x)
    (gL : g * L0 - L0 * g = g * w) (wx : w * x = x * w)
    (hY : g * x * (L0 + k * e) - (L0 + k * e) * (g * x) = -(g * x * (-w + k * D))) :
    xi * e * x - D = e := by sorry
