-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_repr_of_mem_span
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.repr_of_mem_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:41.553489+00:00
-- url     : https://prove2.me/theorems/3546e71d-3406-4205-8a51-59687084736e
-- title:
--   Lattice Index Determinant: repr of mem span
-- statement:
--   The Lattice Index Determinant construction uses the repr of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L72-L78

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.repr_of_mem_span (b : Basis ι K Y)
    (li : LinearIndependent O b) (z : Submodule.span O (Set.range b)) (i : ι) :
    b.repr z i = algebraMap O K ((Basis.span li).repr z i) := by sorry
