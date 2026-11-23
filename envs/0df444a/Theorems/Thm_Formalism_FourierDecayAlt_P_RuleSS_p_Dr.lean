-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_p_Dr
-- name    : Formalism.FourierDecayAlt.P.RuleSS.p_Dr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:20.603751+00:00
-- url     : https://prove2.me/theorems/f2007103-7f5d-4e30-ab10-38e5d4633f7a
-- title:
--   Rule SS: p Dr
-- statement:
--   The Rule SS construction uses the p Dr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L120-L124

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

theorem Formalism.FourierDecayAlt.P.RuleSS.p_Dr (l) : L.p l * L.Dr = L.Dr * (L.p l + algebraMap ℂ A 1) := by sorry
