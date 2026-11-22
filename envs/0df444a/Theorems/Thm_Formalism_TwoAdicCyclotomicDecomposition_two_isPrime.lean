-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_isPrime
-- name    : Formalism.TwoAdicCyclotomicDecomposition.two_isPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:35.688905+00:00
-- url     : https://prove2.me/theorems/1a507daa-ba51-4a67-9f3a-32a3d6c21ca8
-- title:
--   Two Adic Cyclotomic Decomposition: two is Prime
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the two is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L170-L172

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.two_isPrime : (span {(2 : ℤ)}).IsPrime := by sorry
