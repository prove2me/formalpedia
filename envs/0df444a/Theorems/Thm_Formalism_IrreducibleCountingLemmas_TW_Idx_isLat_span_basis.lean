-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_span_basis
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.isLat_span_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:13.045689+00:00
-- url     : https://prove2.me/theorems/f78dcc53-0520-4468-9e53-e651fd668c1d
-- title:
--   Idx: is Lat span basis
-- statement:
--   The Idx construction uses the is Lat span basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L131-L134

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
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
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.isLat_span_basis {d : ℕ} (b : Basis (Fin d) K V) :
    IsLat O K (Submodule.span O (Set.range b)) := by sorry
