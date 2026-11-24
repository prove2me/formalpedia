-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_lin_indep
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.lin_indep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:05.387266+00:00
-- url     : https://prove2.me/theorems/dbed80e0-eeae-4c4c-9aa1-1b402d1afe6c
-- title:
--   BN: lin indep
-- statement:
--   The BN construction uses the lin indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L277-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L277-L302

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.lin_indep {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (c : (A → K[X]) → K)
    (h : ∀ a : A, ∑ F ∈ t, c F * (F a).nextCoeff = 0) : ∀ F ∈ t, c F = 0 := by sorry
