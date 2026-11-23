-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_add_comm0
-- name    : Formalism.FourierDecayAlt.P.RuleSS.add_comm0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:10.432961+00:00
-- url     : https://prove2.me/theorems/3d497034-7acb-4c40-a075-2e2eee77476e
-- title:
--   Rule SS: add comm0
-- statement:
--   The Rule SS construction uses the add comm0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L54-L56

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

theorem Formalism.FourierDecayAlt.P.RuleSS.add_comm0 {x h : A} (hx : Commute x h) (Y : ℂ) :
    (algebraMap ℂ A Y + x) * h = h * (algebraMap ℂ A Y + x) := by sorry
