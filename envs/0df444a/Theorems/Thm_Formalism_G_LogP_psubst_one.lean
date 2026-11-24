-- Prove2me | Theorems.Thm_Formalism_G_LogP_psubst_one
-- name    : Formalism.G.LogP.psubst_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.979719+00:00
-- url     : https://prove2.me/theorems/2b7edfbd-2b24-49bf-9736-d84d5a8f5a6b
-- title:
--   Log P: psubst one
-- statement:
--   The Log P construction uses the psubst one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L217-L219

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

theorem Formalism.G.LogP.psubst_one {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by sorry
