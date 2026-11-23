-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_ypt_im
-- name    : Formalism.FourierDecayAlt.P.Mx9.ypt_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:26.453345+00:00
-- url     : https://prove2.me/theorems/9612e07c-2d5c-46d9-99a6-2c0745fd22f6
-- title:
--   Mx9: ypt im
-- statement:
--   The Mx9 construction uses the ypt im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L41-L43

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9

theorem Formalism.FourierDecayAlt.P.Mx9.ypt_im {S : Type} (a : Letter ℂ S) (h : a.pt.im = 0) : (ypt a).im = 0 := by sorry
