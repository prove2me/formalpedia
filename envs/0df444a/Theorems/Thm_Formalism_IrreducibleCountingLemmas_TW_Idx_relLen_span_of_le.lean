-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_span_of_le
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_span_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:32.83597+00:00
-- url     : https://prove2.me/theorems/02740d39-2271-4a94-b8e0-e731d790a3b9
-- title:
--   Idx: rel Len span of le
-- statement:
--   The Idx construction uses the rel Len span of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L136-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L136-L167

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

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_span_of_le {d : ℕ} (b : Basis (Fin d) K V) (w : Fin d → V)
    (hw : Submodule.span O (Set.range w) ≤ Submodule.span O (Set.range b))
    (hdet : b.det w ≠ 0) :
    ∃ D : O, algebraMap O K D = b.det w ∧
      relLen (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = Ring.ord O D := by sorry
