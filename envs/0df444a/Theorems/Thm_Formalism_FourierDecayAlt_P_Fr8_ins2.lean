-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ins2
-- name    : Formalism.FourierDecayAlt.P.Fr8.ins2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:35.980089+00:00
-- url     : https://prove2.me/theorems/de2edcf8-695a-460e-bcd2-ad63c43fb2e0
-- title:
--   Fr8: ins2
-- statement:
--   The Fr8 construction uses the ins2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L120-L122

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr8.ins2 (a : S) (p q r s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; r, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 0 * r + eU a 1 1 * s := by sorry
