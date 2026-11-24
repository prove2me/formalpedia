-- Prove2me | Theorems.Thm_Formalism_G_LogCR_agree_truncTotal
-- name    : Formalism.G.LogCR.agree_truncTotal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:05.790363+00:00
-- url     : https://prove2.me/theorems/91d0c300-ce09-410d-ad15-9b6283ade0d9
-- title:
--   Log CR: agree trunc Total
-- statement:
--   The Log CR construction uses the agree trunc Total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean#L50-L53

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

theorem Formalism.G.LogCR.agree_truncTotal [Finite σ] (N : ℕ) (f : MvPowerSeries σ R) :
    Agree N f (truncTotal N f : MvPowerSeries σ R) := by sorry
