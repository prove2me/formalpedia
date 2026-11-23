-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_comm_ofFn
-- name    : Formalism.FourierDecayAlt.P.RuleSS.comm_ofFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:22.132154+00:00
-- url     : https://prove2.me/theorems/e76c1147-bdf4-424f-bf46-7d05c90d0722
-- title:
--   Rule SS: comm of Fn
-- statement:
--   The Rule SS construction uses the comm of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L108-L113

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
omit [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.RuleSS.comm_ofFn {n : ℕ} {x : A} {f : Fin n → A} (h : ∀ i, Commute x (f i)) :
    Commute x (List.ofFn f).prod := by sorry
