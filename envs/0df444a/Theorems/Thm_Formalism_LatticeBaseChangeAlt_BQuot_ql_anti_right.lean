-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_anti_right
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.ql_anti_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:36.982154+00:00
-- url     : https://prove2.me/theorems/8e95f863-860b-414d-ab7d-419f82c9eb38
-- title:
--   BQuot: ql anti right
-- statement:
--   The BQuot construction uses the ql anti right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L40-L41

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
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
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

theorem Formalism.LatticeBaseChangeAlt.BQuot.ql_anti_right {A B B' : Submodule O V} (h : B ≤ B') : ql A B' ≤ ql A B := by sorry
