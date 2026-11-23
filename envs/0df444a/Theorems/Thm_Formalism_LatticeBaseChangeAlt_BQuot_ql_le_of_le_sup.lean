-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_le_sup
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_le_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:25.857517+00:00
-- url     : https://prove2.me/theorems/63eb6190-96f4-46aa-8a77-2548188edc3f
-- title:
--   BQuot: ql le of le sup
-- statement:
--   The BQuot construction uses the ql le of le sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L52-L53

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

theorem Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_le_sup {A A' B : Submodule O V} (h : A ≤ A' ⊔ B) : ql A B ≤ ql A' B := by sorry
