-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_add_left
-- name    : Formalism.GradedWeylDivisibility.lfockq_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:18.747862+00:00
-- url     : https://prove2.me/theorems/01b5f36e-d84a-4a09-8339-31b21cd3cd7f
-- title:
--   Graded Weyl Divisibility: lfockq add left
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L40-L47

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

theorem Formalism.GradedWeylDivisibility.lfockq_add_left (f f' g : MvPolynomial σ ℚ) :
    fockQ (f + f') g = fockQ f g + fockQ f' g := by sorry
