-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_smul_left
-- name    : Formalism.GradedWeylDivisibility.lfockq_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:44.266799+00:00
-- url     : https://prove2.me/theorems/ca4c9159-0a7c-44fb-bed9-ebd4c8ae9b15
-- title:
--   Graded Weyl Divisibility: lfockq smul left
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L49-L53

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
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
variable {σ : Type*}

theorem Formalism.GradedWeylDivisibility.lfockq_smul_left (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g := by sorry
