-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_asm
-- name    : Formalism.FourierDecayAlt.P.Fr8.asm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:04:30.331259+00:00
-- url     : https://prove2.me/theorems/1be1f18a-8aa4-4fe4-898e-1cc879c3adcf
-- title:
--   Fr8: asm
-- statement:
--   The Fr8 construction uses the asm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L251-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L251-L258

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

theorem Formalism.FourierDecayAlt.P.Fr8.asm {R : Type} [Ring R] [StarRing R] {F Fi d U D Λ : R} (hFFi : F * Fi = 1)
    (hU : d * U = star Λ * d) :
    star F * d * F * (Fi * (U * D * Λ) * F) = star (Λ * F) * (d * D) * (Λ * F) := by sorry
