-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_cut_admissible
-- name    : Formalism.FourierDecayAlt.P.cut_admissible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:07.470814+00:00
-- url     : https://prove2.me/theorems/dca80171-c431-401b-b847-961e3645a37e
-- title:
--   P: cut admissible
-- statement:
--   The P construction uses the cut admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L65-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L65-L91

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
open Mx9

theorem Formalism.FourierDecayAlt.P.cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by sorry
