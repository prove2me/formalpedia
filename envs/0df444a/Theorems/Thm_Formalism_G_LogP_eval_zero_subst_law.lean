-- Prove2me | Theorems.Thm_Formalism_G_LogP_eval_zero_subst_law
-- name    : Formalism.G.LogP.eval_zero_subst_law
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:25.278122+00:00
-- url     : https://prove2.me/theorems/d0b5d5f2-e65a-4c50-be78-d3eb547b565c
-- title:
--   Log P: eval zero subst law
-- statement:
--   The Log P construction uses the eval zero subst law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L81-L86

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)

theorem Formalism.G.LogP.eval_zero_subst_law (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (φ.subst F.toPowerSeries) = φ := by sorry
