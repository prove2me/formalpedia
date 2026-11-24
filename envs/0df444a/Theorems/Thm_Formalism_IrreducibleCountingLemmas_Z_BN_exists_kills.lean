-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_kills
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.exists_kills
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:42.533208+00:00
-- url     : https://prove2.me/theorems/078ba28d-cf71-407b-8e53-16853708594a
-- title:
--   BN: exists kills
-- statement:
--   The BN construction uses the exists kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L237-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L237-L269

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

theorem Formalism.IrreducibleCountingLemmas.Z.BN.exists_kills {K A : Type} [Field K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (h0 : (cp K S0 : A → K[X]) ∉ t) :
    ∃ a : A, Kills t a ∧ ∃ s : S0, a • s ≠ 0 := by sorry
