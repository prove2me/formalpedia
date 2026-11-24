-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_charpoly_mem_closure_simple
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_mem_closure_simple
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:06.277454+00:00
-- url     : https://prove2.me/theorems/8f534dc0-ca9d-479f-a9fb-7a9490c1f4f9
-- title:
--   BN: charpoly mem closure simple
-- statement:
--   The BN construction uses the charpoly mem closure simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L58-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L58-L90

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_mem_closure_simple {k A : Type} [Field k] [Ring A] [Algebra k A] :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
      [FiniteDimensional k V], Module.finrank k V = n →
      (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) := by sorry
