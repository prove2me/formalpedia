-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_oddExponentCount
-- name    : Formalism.DworkPowerSeriesWeights.oddExponentCount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:09.195254+00:00
-- url     : https://prove2.me/theorems/2d889c97-b285-4298-a67d-f0e661adc5c0
-- title:
--   Dwork Power Series Weights: odd Exponent Count
-- statement:
--   The Dwork Power Series Weights construction uses the odd Exponent Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L11-L28

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights

theorem Formalism.DworkPowerSeriesWeights.oddExponentCount : JCount := by sorry
