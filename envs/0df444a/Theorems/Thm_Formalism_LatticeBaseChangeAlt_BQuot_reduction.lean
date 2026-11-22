-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_reduction
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.reduction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:47.404099+00:00
-- url     : https://prove2.me/theorems/51145b51-4a73-42d3-9c97-74f2f1da906a
-- title:
--   BQuot: reduction
-- statement:
--   The BQuot construction uses the reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L90-L97

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

theorem Formalism.LatticeBaseChangeAlt.BQuot.reduction (X Θ N₀ T NK : Submodule O V) (h1 : N₀ ≤ Θ) (h2 : T ≤ Θ) :
    ql (X ⊔ Θ) Θ ≤ ql ((X ⊓ NK) ⊔ N₀) N₀ + ql X ((X ⊓ NK) ⊔ T) := by sorry
