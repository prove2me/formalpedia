-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_c_wt
-- name    : Formalism.FourierDecayAlt.P.Fr3.c_wt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:12.847147+00:00
-- url     : https://prove2.me/theorems/39707624-939a-4323-8bd1-bceb3b22edef
-- title:
--   Fr3: c wt
-- statement:
--   The Fr3 construction uses the c wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L178-L180

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr3.c_wt (hf : IsFrame L f) : Commute f.c (wt L) := by sorry
