-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_lengthBaseChangeLocal
-- name    : Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:32.708192+00:00
-- url     : https://prove2.me/theorems/cb48ad86-7761-400c-883a-0895bccee94c
-- title:
--   Lattice Base Change Alt: length Base Change Local
-- statement:
--   The Lattice Base Change Alt construction uses the length Base Change Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L47-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L47-L72

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct

theorem Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal : LengthBaseChangeLocal := by sorry
