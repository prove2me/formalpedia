-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_val_unique
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.val_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:32.40379+00:00
-- url     : https://prove2.me/theorems/257add03-7cd5-48fc-b947-bc302f87e3c6
-- title:
--   Idx: val unique
-- statement:
--   The Idx construction uses the val unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L25-L34

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
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.val_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a b : ℤ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a = algebraMap O K v * algebraMap O K ϖ ^ b) :
    a = b := by sorry
