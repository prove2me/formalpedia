-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_brauer_nesbitt_algebra
-- name    : Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt_algebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:23.999554+00:00
-- url     : https://prove2.me/theorems/44f85fa0-c0de-4213-912f-375967aef2d2
-- title:
--   Z: brauer nesbitt algebra
-- statement:
--   The Z construction uses the brauer nesbitt algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean#L125-L127

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt_algebra : BrauerNesbittAlg := by sorry
