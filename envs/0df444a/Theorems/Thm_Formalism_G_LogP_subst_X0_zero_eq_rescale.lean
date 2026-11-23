-- Prove2me | Theorems.Thm_Formalism_G_LogP_subst_X0_zero_eq_rescale
-- name    : Formalism.G.LogP.subst_X0_zero_eq_rescale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:41.903156+00:00
-- url     : https://prove2.me/theorems/e0f6e4a5-6dce-48d9-b897-5d06f1203e92
-- title:
--   Log P: subst X0 zero eq rescale
-- statement:
--   The Log P construction uses the subst X0 zero eq rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L221-L226

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

theorem Formalism.G.LogP.subst_X0_zero_eq_rescale (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = rescale ![1, 0] Φ := by sorry
