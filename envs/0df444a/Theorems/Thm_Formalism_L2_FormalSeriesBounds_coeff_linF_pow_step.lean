-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_linF_pow_step
-- name    : Formalism.L2.FormalSeriesBounds.coeff_linF_pow_step
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:10.834812+00:00
-- url     : https://prove2.me/theorems/507962be-3160-4d51-ac4a-6906335a7e7d
-- title:
--   Formal Series Bounds: coeff lin F pow step
-- statement:
--   The Formal Series Bounds construction uses the coeff lin F pow step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L34-L42

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

theorem Formalism.L2.FormalSeriesBounds.coeff_linF_pow_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) (k : ℕ) :
    coeff (m + Finsupp.single w 1) (linF lam ^ (k + 1)) * ((m w : K) + 1)
      = ((k : K) + 1) * lam w * coeff m (linF lam ^ k) := by sorry
