-- Prove2me | Theorems.Thm_Formalism_GrowthSums_cappedGainSubLE
-- name    : Formalism.GrowthSums.cappedGainSubLE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:15.034087+00:00
-- url     : https://prove2.me/theorems/1cf6784e-610a-41ec-8878-944dcfdbad7b
-- title:
--   Growth Sums: capped Gain Sub LE
-- statement:
--   The Growth Sums construction uses the capped Gain Sub LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/PathBasisOfCount.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/PathBasisOfCount.lean#L23-L37

import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
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
open Finset
open Formalism Formalism.GrowthSums

theorem Formalism.GrowthSums.cappedGainSubLE : CappedGainSubLE := by sorry
