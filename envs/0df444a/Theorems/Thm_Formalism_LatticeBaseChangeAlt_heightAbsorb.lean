-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_heightAbsorb
-- name    : Formalism.LatticeBaseChangeAlt.heightAbsorb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:40.264936+00:00
-- url     : https://prove2.me/theorems/8db89f2d-e5c8-4eb0-b62d-3bc7a326a5c6
-- title:
--   Lattice Base Change Alt: height Absorb
-- statement:
--   The Lattice Base Change Alt construction uses the height Absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/FilIntegerStep.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/FilIntegerStep.lean#L49-L53

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt

theorem Formalism.LatticeBaseChangeAlt.heightAbsorb : HeightAbsorb := by sorry
