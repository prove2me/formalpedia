-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_mem_span_basisFun
-- name    : Formalism.LatticeBaseChangeAlt.BQuot.mem_span_basisFun
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:03.173833+00:00
-- url     : https://prove2.me/theorems/14c3baed-0a1e-411f-bdb8-90a52f90c715
-- title:
--   BQuot: mem span basis Fun
-- statement:
--   The BQuot construction uses the mem span basis Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/MemSpanBasisFun.lean#L148-L155

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
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem Formalism.LatticeBaseChangeAlt.BQuot.mem_span_basisFun (n : ℕ) (y : Fin n → K) (h : ∀ i, ∃ a : O, y i = algebraMap O K a) :
    y ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin n))) := by sorry
