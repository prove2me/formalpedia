-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cbi
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_mem_cbi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:00:54.6092+00:00
-- url     : https://prove2.me/theorems/112ebe42-3992-45f7-8135-26903d07aff1
-- title:
--   Level Data: inv mem cbi
-- statement:
--   The Level Data construction uses the inv mem cbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L46-L46

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

theorem Formalism.FourierDecayAlt.R.LevelData.inv_mem_cbi (l) : L.cbi l ∈ L.fns := by sorry
