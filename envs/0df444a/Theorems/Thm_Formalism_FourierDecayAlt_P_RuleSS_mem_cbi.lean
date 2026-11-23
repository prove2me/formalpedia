-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_cbi
-- name    : Formalism.FourierDecayAlt.P.RuleSS.mem_cbi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:04.689803+00:00
-- url     : https://prove2.me/theorems/14276d0e-28af-42a0-9256-0ae94450464d
-- title:
--   Rule SS: mem cbi
-- statement:
--   The Rule SS construction uses the mem cbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L101-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L101-L101

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

theorem Formalism.FourierDecayAlt.P.RuleSS.mem_cbi (l) : L.cbi l ∈ L.fns := by sorry
