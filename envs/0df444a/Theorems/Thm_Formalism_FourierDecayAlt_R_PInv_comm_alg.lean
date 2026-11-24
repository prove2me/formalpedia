-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_comm_alg
-- name    : Formalism.FourierDecayAlt.R.PInv.comm_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:41.731901+00:00
-- url     : https://prove2.me/theorems/2c87eb34-15aa-4d5c-8304-55ef06c0424e
-- title:
--   PInv: comm alg
-- statement:
--   The PInv construction uses the comm alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L83-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L83-L83

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

theorem Formalism.FourierDecayAlt.R.PInv.comm_alg (x : A) (y : ℂ) : Commute x (algebraMap ℂ A y) := by sorry
