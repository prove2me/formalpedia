-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_of_determinant
-- name    : Formalism.IrreducibleCountingLemmas.TW.index_of_determinant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:40.988349+00:00
-- url     : https://prove2.me/theorems/6a14c5fd-aa6e-4536-b247-73421f4506d4
-- title:
--   TW: index of determinant
-- statement:
--   The TW construction uses the index of determinant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L38-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L38-L76

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.index_of_determinant : IndexDet := by sorry
