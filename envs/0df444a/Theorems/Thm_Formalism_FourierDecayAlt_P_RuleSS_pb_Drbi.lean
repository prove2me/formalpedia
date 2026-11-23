-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_pb_Drbi
-- name    : Formalism.FourierDecayAlt.P.RuleSS.pb_Drbi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:34.128189+00:00
-- url     : https://prove2.me/theorems/48049c11-ec00-4f3f-9635-c15eaca59e07
-- title:
--   Rule SS: pb Drbi
-- statement:
--   The Rule SS construction uses the pb Drbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L138-L142

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem Formalism.FourierDecayAlt.P.RuleSS.pb_Drbi (l) : L.pb l * L.Drbi = L.Drbi * (L.pb l + algebraMap ℂ A (-1)) := by sorry
