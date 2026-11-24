-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_symm
-- name    : Formalism.GradedWeylDivisibility.lfockq_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:56.197132+00:00
-- url     : https://prove2.me/theorems/65b1b248-de14-4b98-9d10-8f07ffcaa6b3
-- title:
--   Graded Weyl Divisibility: lfockq symm
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L22-L26

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

theorem Formalism.GradedWeylDivisibility.lfockq_symm (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by sorry
