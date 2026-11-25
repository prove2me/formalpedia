-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_LogEx_poinc
-- name    : Formalism.L2.FormalSeriesBounds.LogEx.poinc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:11.678689+00:00
-- url     : https://prove2.me/theorems/193c829c-3223-4687-b4ec-439b26acbab3
-- title:
--   Log Ex: poinc
-- statement:
--   The Log Ex construction uses the poinc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PoincEx.lean#L11-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PoincEx.lean#L11-L68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PoincEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.LogEx

theorem Formalism.L2.FormalSeriesBounds.LogEx.poinc {σ : Type} [Fintype σ] {K : Type} [Field K] [CharZero K] (ω : σ → MvPowerSeries σ K)
    (hω : ∀ j l, MvPowerSeries.pderiv K j (ω l) = MvPowerSeries.pderiv K l (ω j)) :
    ∃ g : MvPowerSeries σ K, MvPowerSeries.constantCoeff g = 0 ∧ ∀ j, MvPowerSeries.pderiv K j g = ω j := by sorry
