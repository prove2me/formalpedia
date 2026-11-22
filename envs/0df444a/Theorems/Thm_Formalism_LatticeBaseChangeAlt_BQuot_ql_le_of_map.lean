-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:52.079605+00:00
-- url     : https://prove2.me/theorems/d2efeb60-f398-418e-9be3-4e4e92e25626
-- title:
--   BQuot: ql le of map
-- statement:
--   The BQuot construction uses the ql le of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L29-L35

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

theorem Formalism.LatticeBaseChangeAlt.BQuot.ql_le_of_map {A S : Submodule O V} {L P : Submodule O W} (f : ↥A →ₗ[O] W)
    (h1 : ∀ x, f x ∈ L) (h2 : ∀ x, f x ∈ P → (x : V) ∈ S) : ql A S ≤ ql L P := by sorry
