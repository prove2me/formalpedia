-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_detProductRest
-- name    : Formalism.LatticeBaseChangeAlt.detProductRest
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:24.737406+00:00
-- url     : https://prove2.me/theorems/672a3d8a-fb95-4302-975f-1e8ebaf2fbae
-- title:
--   Lattice Base Change Alt: det Product Rest
-- statement:
--   The Lattice Base Change Alt construction uses the det Product Rest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MinimumChainBounds.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MinimumChainBounds.lean#L34-L43

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_AlternatingBinomial
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MinimumChainBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Real

theorem Formalism.LatticeBaseChangeAlt.detProductRest : DetProductRest := by sorry
