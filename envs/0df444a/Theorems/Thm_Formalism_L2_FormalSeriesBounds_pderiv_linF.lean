-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_linF
-- name    : Formalism.L2.FormalSeriesBounds.pderiv_linF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:00.845803+00:00
-- url     : https://prove2.me/theorems/90f2e16a-2a80-4fe4-b513-8f8e8b46f6ee
-- title:
--   Formal Series Bounds: pderiv lin F
-- statement:
--   The Formal Series Bounds construction uses the pderiv lin F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean#L24-L32

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

theorem Formalism.L2.FormalSeriesBounds.pderiv_linF (lam : τ → K) (w : τ) : pderiv K w (linF lam) = C (lam w) := by sorry
