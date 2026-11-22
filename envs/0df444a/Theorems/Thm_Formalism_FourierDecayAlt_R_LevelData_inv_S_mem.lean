-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_mem
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_S_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:19:59.19453+00:00
-- url     : https://prove2.me/theorems/7a1c49e8-4baf-46b2-9ef1-b7b51e06d0e1
-- title:
--   Level Data: inv S mem
-- statement:
--   The Level Data construction uses the inv S mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L85-L85

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

theorem Formalism.FourierDecayAlt.R.LevelData.inv_S_mem {x : A} (hx : x ∈ L.fns) : x ∈ Algebra.adjoin ℂ L.fns := by sorry
