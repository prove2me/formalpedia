-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_LogEx_poinc_ex
-- name    : Formalism.L2.FormalSeriesBounds.LogEx.poinc_ex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:36.942947+00:00
-- url     : https://prove2.me/theorems/ce657b7f-7838-4520-8bdf-97b77c5b20c3
-- title:
--   Log Ex: poinc ex
-- statement:
--   The Log Ex construction uses the poinc ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PoincEx.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PoincEx.lean#L7-L9

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

theorem Formalism.L2.FormalSeriesBounds.LogEx.poinc_ex {σ K : Type} [CommRing K] (c : (σ →₀ ℕ) → K) :
    ∃ g : MvPowerSeries σ K, ∀ μ, coeff μ g = c μ := by sorry
