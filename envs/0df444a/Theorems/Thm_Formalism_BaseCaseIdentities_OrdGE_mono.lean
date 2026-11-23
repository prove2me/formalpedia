-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
-- name    : Formalism.BaseCaseIdentities.OrdGE.mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:59.913559+00:00
-- url     : https://prove2.me/theorems/955c2ad9-5b99-4e4d-b3df-eb5d2f3a53b3
-- title:
--   Ord GE: mono
-- statement:
--   The Ord GE construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L13-L15

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

theorem Formalism.BaseCaseIdentities.OrdGE.mono {a b : ℕ} {f : MvPowerSeries Z k} (h : a ≤ b) (hf : OrdGE b f) : OrdGE a f := by sorry
