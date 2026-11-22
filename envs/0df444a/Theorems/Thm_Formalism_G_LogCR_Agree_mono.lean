-- Prove2me | Theorems.Thm_Formalism_G_LogCR_Agree_mono
-- name    : Formalism.G.LogCR.Agree.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:01.023784+00:00
-- url     : https://prove2.me/theorems/8cc740ef-9610-496b-90ba-37d8e9f08e42
-- title:
--   Agree: mono
-- statement:
--   The Agree construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
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
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}

theorem Formalism.G.LogCR.Agree.mono {N M : ℕ} {f g : MvPowerSeries σ R} (h : Agree N f g) (hMN : M ≤ N) :
    Agree M f g := by sorry
