-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_gHadamard
-- name    : Formalism.LatticeBaseChangeAlt.gHadamard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:31.631252+00:00
-- url     : https://prove2.me/theorems/2e024f66-51a1-4142-a963-192dc48433fa
-- title:
--   Lattice Base Change Alt: g Hadamard
-- statement:
--   The Lattice Base Change Alt construction uses the g Hadamard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/GAdjugateNormBound.lean#L46-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/GAdjugateNormBound.lean#L46-L93

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_GFiniteOrderUnipotent
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_GAdjugateNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.LatticeBaseChangeAlt

theorem Formalism.LatticeBaseChangeAlt.gHadamard : GHadamard := by sorry
