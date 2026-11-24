-- Prove2me | Theorems.Thm_Formalism_G0_TopsCount_sum_ite_lt
-- name    : Formalism.G0.TopsCount.sum_ite_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:29.630033+00:00
-- url     : https://prove2.me/theorems/b6491fc9-3c61-4c47-8e1b-ac0de8887648
-- title:
--   Tops Count: sum ite lt
-- statement:
--   The Tops Count construction uses the sum ite lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L55-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L55-L70

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount

theorem Formalism.G0.TopsCount.sum_ite_lt (m : ℕ) (δ : ℝ) (K : ℕ) :
    ∑ j ∈ range (m + 1), (if j < K then a m δ j else 0) = A m δ K := by sorry
