-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_zero_mvExp
-- name    : Formalism.L2.FormalSeriesBounds.coeff_zero_mvExp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:02.267522+00:00
-- url     : https://prove2.me/theorems/c49452b9-9aaf-4d31-bc15-18e4403276b9
-- title:
--   Formal Series Bounds: coeff zero mv Exp
-- statement:
--   The Formal Series Bounds construction uses the coeff zero mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L71-L73

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
variable [CharZero K]

theorem Formalism.L2.FormalSeriesBounds.coeff_zero_mvExp (h : MvPowerSeries τ K) : coeff 0 (mvExp h) = 1 := by sorry
