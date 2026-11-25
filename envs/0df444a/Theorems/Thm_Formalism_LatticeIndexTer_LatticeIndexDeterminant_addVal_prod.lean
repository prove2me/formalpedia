-- Prove2me | Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_addVal_prod
-- name    : Formalism.LatticeIndexTer.LatticeIndexDeterminant.addVal_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:33.122001+00:00
-- url     : https://prove2.me/theorems/4fdb70f6-9025-45ef-abff-ff596377cb95
-- title:
--   Lattice Index Determinant: add Val prod
-- statement:
--   The Lattice Index Determinant construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxDet.lean#L11-L19

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

theorem Formalism.LatticeIndexTer.LatticeIndexDeterminant.addVal_prod {O ι : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by sorry
