-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cb
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_mem_cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:05.143375+00:00
-- url     : https://prove2.me/theorems/d84b75d7-2478-4b27-a35b-eaea37fbd960
-- title:
--   Level Data: inv mem cb
-- statement:
--   The Level Data construction uses the inv mem cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L45-L45

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem Formalism.FourierDecayAlt.R.LevelData.inv_mem_cb (l) : L.cb l ∈ L.fns := by sorry
