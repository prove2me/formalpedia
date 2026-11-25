-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mvExp_linF_step
-- name    : Formalism.L2.FormalSeriesBounds.coeff_mvExp_linF_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:03.742324+00:00
-- url     : https://prove2.me/theorems/537a85c7-56b3-4720-ab78-d06f46e32460
-- title:
--   Formal Series Bounds: coeff mv Exp lin F step
-- statement:
--   The Formal Series Bounds construction uses the coeff mv Exp lin F step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L54-L69

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

theorem Formalism.L2.FormalSeriesBounds.coeff_mvExp_linF_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) :
    coeff (m + Finsupp.single w 1) (mvExp (linF lam)) * ((m w : K) + 1)
      = lam w * coeff m (mvExp (linF lam)) := by sorry
