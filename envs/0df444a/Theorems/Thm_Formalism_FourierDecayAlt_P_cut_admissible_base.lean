-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_cut_admissible_base
-- name    : Formalism.FourierDecayAlt.P.cut_admissible_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:43.400879+00:00
-- url     : https://prove2.me/theorems/d56635dc-f813-42bd-ae70-6b28e24d2a66
-- title:
--   P: cut admissible base
-- statement:
--   The P construction uses the cut admissible base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L93-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L93-L130

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

theorem Formalism.FourierDecayAlt.P.cut_admissible_base : Formalism.FourierDecayAlt.M.CutAdmBase := by sorry
