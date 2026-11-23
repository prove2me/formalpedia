-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_triangle
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.ql_triangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:24.233793+00:00
-- url     : https://prove2.me/theorems/3acf7719-ab30-4916-951c-53ca96711829
-- title:
--   BQuot: ql triangle
-- statement:
--   The BQuot construction uses the ql triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L84-L88

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

theorem Formalism.LatticeBaseChangeAlt.BQuot.ql_triangle (A B C : Submodule O V) : ql A C ≤ ql A B + ql B C := by sorry
