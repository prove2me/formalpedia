-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mon2
-- name    : Formalism.FourierDecayAlt.P.Fr8.mon2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:04:33.183069+00:00
-- url     : https://prove2.me/theorems/c530d017-b89c-4c29-8eaa-1fbfcf7867c8
-- title:
--   Fr8: mon2
-- statement:
--   The Fr8 construction uses the mon2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L20-L23

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
variable {M : Type} [Monoid M]

theorem Formalism.FourierDecayAlt.P.Fr8.mon2 {z zi w wi g gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (hg : gi * g = 1) :
    z * w * gi * (g * wi) * (zi * g) = g := by sorry
