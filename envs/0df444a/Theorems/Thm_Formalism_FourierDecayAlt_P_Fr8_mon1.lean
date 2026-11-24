-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mon1
-- name    : Formalism.FourierDecayAlt.P.Fr8.mon1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:04:56.994039+00:00
-- url     : https://prove2.me/theorems/0a92c125-9912-4467-9ceb-fe63dc5d3911
-- title:
--   Fr8: mon1
-- statement:
--   The Fr8 construction uses the mon1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L13-L18

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

theorem Formalism.FourierDecayAlt.P.Fr8.mon1 {z zi w wi gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (c1 : Commute gi zi)
    (c2 : Commute w zi) (c3 : Commute gi wi) : z * w * gi * zi * wi = gi := by sorry
