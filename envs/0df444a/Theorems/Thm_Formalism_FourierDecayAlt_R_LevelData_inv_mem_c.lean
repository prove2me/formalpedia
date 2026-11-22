-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_c
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_mem_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:02.073846+00:00
-- url     : https://prove2.me/theorems/fe021ef9-e25c-415d-a9fd-8c39949b1f81
-- title:
--   Level Data: inv mem c
-- statement:
--   The Level Data construction uses the inv mem c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L47-L47

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

theorem Formalism.FourierDecayAlt.R.LevelData.inv_mem_c (l) : L.c l ∈ L.fns := by sorry
