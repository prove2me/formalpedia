-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_valuation_unique
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.valuation_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:29.289342+00:00
-- url     : https://prove2.me/theorems/1608c5f2-8d33-460d-adcd-219afd5f19e7
-- title:
--   Idx: valuation unique
-- statement:
--   The Idx construction uses the valuation unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean#L12-L23

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

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.valuation_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a : ℤ) (m : ℕ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a
      = algebraMap O K v * algebraMap O K ϖ ^ (a + (m : ℤ))) : m = 0 := by sorry
