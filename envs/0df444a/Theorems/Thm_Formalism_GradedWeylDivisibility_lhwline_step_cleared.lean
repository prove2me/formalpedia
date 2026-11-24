-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_step_cleared
-- name    : Formalism.GradedWeylDivisibility.lhwline_step_cleared
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:05.822234+00:00
-- url     : https://prove2.me/theorems/11822bbe-4a77-4cae-b38a-5eadf4b9a323
-- title:
--   Graded Weyl Divisibility: lhwline step cleared
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline step cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L192-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L192-L221

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_step_cleared (k : ℕ) (hr : k < r) (hn : k < n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hp : y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0) :
    lhwline_cleared (k + 1) (highestWeightLineUpdate ⟨k, hr⟩ ⟨k, hn⟩ y) := by sorry
