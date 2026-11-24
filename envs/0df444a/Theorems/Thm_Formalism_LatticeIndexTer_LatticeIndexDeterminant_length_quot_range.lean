-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_length_quot_range
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.length_quot_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:53.564329+00:00
-- url     : https://prove2.me/theorems/a109ffc8-e057-449a-b394-fffa45896c2f
-- title:
--   Lattice Index Determinant: length quot range
-- statement:
--   The Lattice Index Determinant construction uses the length quot range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L21-L25

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

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.length_quot_range {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (φ : M →ₗ[O] M) (hφ : Function.Injective φ) :
    Module.length O (M ⧸ LinearMap.range φ) = IsDiscreteValuationRing.addVal O (LinearMap.det φ) := by sorry
