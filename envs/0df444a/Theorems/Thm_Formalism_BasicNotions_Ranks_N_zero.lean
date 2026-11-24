-- Prove2me | Theorems.Thm_Formalism_BasicNotions_Ranks_N_zero
-- name    : Formalism.BasicNotions.Ranks.N_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:47.282514+00:00
-- url     : https://prove2.me/theorems/757316c0-5882-4b1a-9bdc-e49ebfafc804
-- title:
--   Ranks: N zero
-- statement:
--   The Ranks construction uses the N zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataForms.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataForms.lean#L91-L92

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField

theorem Formalism.BasicNotions.Ranks.N_zero (R : Ranks) : R.N 0 = R.k := by sorry
