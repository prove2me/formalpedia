-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_mem_closure
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.cp_mem_closure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:46.603367+00:00
-- url     : https://prove2.me/theorems/319b0ce9-2d8f-466c-bcb4-825f382489df
-- title:
--   BN: cp mem closure
-- statement:
--   The BN construction uses the cp mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L92-L95

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN

theorem Formalism.IrreducibleCountingLemmas.Z.BN.cp_mem_closure {k A : Type} [Field k] [Ring A] [Algebra k A] (V : Type) [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] :
    (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) := by sorry
