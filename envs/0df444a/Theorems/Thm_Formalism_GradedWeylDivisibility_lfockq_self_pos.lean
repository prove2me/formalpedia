-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_self_pos
-- name    : Formalism.GradedWeylDivisibility.lfockq_self_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:13.313135+00:00
-- url     : https://prove2.me/theorems/302233fe-d740-45f4-8707-9cae4696f0a5
-- title:
--   Graded Weyl Divisibility: lfockq self pos
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq self pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LFockqLemmas.lean#L28-L38

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

theorem Formalism.GradedWeylDivisibility.lfockq_self_pos (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockQ f f := by sorry
